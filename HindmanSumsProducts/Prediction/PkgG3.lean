import HindmanSumsProducts.Prediction.Projections
import HindmanSumsProducts.Concatenation

/-! Helpers for the cellwise inverse theorem step in S5-G. -/

open scoped BigOperators NNReal Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace HindmanSumsProducts.Prediction

/-! A private copy of the finite cell system, kept here because this module is imported by
`Subgroup.lean` before the original cell declarations. -/

def p_g3_cellOrder {K : ℕ} (A : Parameters K) (N : ℕ) (l : Fin K) : ℕ :=
  A.H N l / A.M N

def p_g3_fullIntervals {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset ℤ :=
  Finset.Ico (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ((A.X N i : ℤ) ^ 2 / A.H N l)

def p_g3_cells {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset (ℤ × ℕ) :=
  p_g3_fullIntervals A N i l ×ˢ Finset.range (A.M N)

def p_g3_cellPoint {K : ℕ} (A : Parameters K) (N : ℕ) (l : Fin K)
    (C : ℤ × ℕ) (x : ℕ) : ℤ :=
  C.1 * A.H N l + C.2 + A.M N * x

def p_g3_cellPairs {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) :
    Finset ((ℤ × ℕ) × ℕ) :=
  (p_g3_cells A N i l).product (Finset.range (p_g3_cellOrder A N l))

def p_g3_cellPointImage {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset ℤ :=
  (p_g3_cellPairs A N i l).image
    (fun z : (ℤ × ℕ) × ℕ => p_g3_cellPoint A N l z.1 z.2)

def p_g3_partialIntervals {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) : Finset ℤ :=
  Finset.Ico (A.X N i : ℤ) ((A.X N i + A.H N l : ℕ) : ℤ) ∪
    Finset.Ico (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ) ((A.X N i) ^ 2 : ℤ)

noncomputable def p_g3_cellMass {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (C : ℤ × ℕ) : ℝ :=
  ∑ x ∈ Finset.range (p_g3_cellOrder A N l), mu A N i (p_g3_cellPoint A N l C x)

noncomputable def p_g3_totalCellMass {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K) : ℝ :=
  ∑ C ∈ p_g3_cells A N i l, p_g3_cellMass A N i l C

noncomputable def p_g3_cellWeight {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (C : ℤ × ℕ) : ℝ :=
  p_g3_cellMass A N i l C /
    (∑ C' ∈ p_g3_cells A N i l, p_g3_cellMass A N i l C')

noncomputable def p_g3_localCellMoment {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (t : ℕ) (C : ℤ × ℕ) (h : ℤ → ℝ)
    [NeZero (p_g3_cellOrder A N l)] : ℝ :=
  (SubgroupBox.boxMoment
    (List.replicate t (⊤ : AddSubgroup (ZMod (p_g3_cellOrder A N l))))
    (fun x => ((h (p_g3_cellPoint A N l C x.val) : ℝ) : ℂ))).re

noncomputable def p_g3_cellGlobalMoment {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (t : ℕ) (h : ℤ → ℝ) : ℝ :=
  if hq : p_g3_cellOrder A N l = 0 then 0 else
    haveI : NeZero (p_g3_cellOrder A N l) := ⟨hq⟩
    ∑ C ∈ p_g3_cells A N i l, p_g3_cellWeight A N i l C *
      p_g3_localCellMoment A N i l t C h

noncomputable def p_g3_goodCells {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (t : ℕ) (h : ℤ → ℝ) (lam : ℝ)
    [NeZero (p_g3_cellOrder A N l)] : Finset (ℤ × ℕ) :=
  (p_g3_cells A N i l).filter
    (fun C => lam / 2 ≤ p_g3_localCellMoment A N i l t C h)

theorem p_g3_point_div_mod {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (hq : 0 < p_g3_cellOrder A N l) (C : ℤ × ℕ)
    (hC : C ∈ p_g3_cells A N i l) (x : ℕ)
    (hx : x < p_g3_cellOrder A N l) :
    p_g3_cellPoint A N l C x / (A.H N l : ℤ) = C.1 ∧
      p_g3_cellPoint A N l C x % (A.H N l : ℤ) = (C.2 : ℤ) + (A.M N : ℤ) * x := by
  have hMpos : 0 < A.M N := A.Mpos N
  have hMq : A.M N * p_g3_cellOrder A N l = A.H N l := by
    dsimp [p_g3_cellOrder]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
  have hCmem : C.1 ∈ p_g3_fullIntervals A N i l ∧ C.2 < A.M N := by
    simpa [p_g3_cells] using hC
  have hremNat : C.2 + A.M N * x < A.H N l := by
    have hx1 : x + 1 ≤ p_g3_cellOrder A N l := Nat.succ_le_of_lt hx
    have hstep : A.M N * (x + 1) ≤ A.M N * p_g3_cellOrder A N l :=
      Nat.mul_le_mul_left _ hx1
    have hsmall : C.2 + A.M N * x < A.M N * (x + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hMq] at hstep
    exact hsmall.trans_le hstep
  have hrem0 : (0 : ℤ) ≤ (C.2 : ℤ) + (A.M N : ℤ) * x := by positivity
  have hremLt : (C.2 : ℤ) + (A.M N : ℤ) * x < (A.H N l : ℤ) := by
    exact_mod_cast hremNat
  have hrepr : (C.2 : ℤ) + (A.M N : ℤ) * x + (A.H N l : ℤ) * C.1 =
      p_g3_cellPoint A N l C x := by
    simp [p_g3_cellPoint]
    ring
  have hHpos : 0 < (A.H N l : ℤ) := by exact_mod_cast A.Hpos N l
  have huniq := (Int.ediv_emod_unique'' (a := p_g3_cellPoint A N l C x)
    (b := (A.H N l : ℤ)) (r := (C.2 : ℤ) + (A.M N : ℤ) * x) (q := C.1)
    hHpos.ne').2 ⟨hrepr, hrem0, by simpa [abs_of_pos hHpos] using hremLt⟩
  exact huniq

private theorem p_g3_fullInterval_bounds {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (k : ℤ) (hk : k ∈ p_g3_fullIntervals A N i l) :
    (A.X N i : ℤ) ≤ k * (A.H N l : ℤ) ∧
      (k + 1) * (A.H N l : ℤ) ≤ (A.X N i : ℤ) ^ 2 := by
  have hk' : (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ≤ k ∧
      k < ((A.X N i : ℤ) ^ 2 / A.H N l) := by
    simpa [p_g3_fullIntervals] using Finset.mem_Ico.mp hk
  have hHpos : 0 < (A.H N l : ℤ) := by exact_mod_cast A.Hpos N l
  have hHne : (A.H N l : ℤ) ≠ 0 := hHpos.ne'
  have hremLo := Int.emod_nonneg ((A.X N i : ℤ) + A.H N l - 1) hHne
  have hremLoLt := Int.emod_lt_abs ((A.X N i : ℤ) + A.H N l - 1) hHne
  have hdivLo := Int.emod_add_mul_ediv ((A.X N i : ℤ) + A.H N l - 1) (A.H N l : ℤ)
  have hLoMul : (A.X N i : ℤ) ≤ (A.H N l : ℤ) *
      (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) := by
    have hremPosLt : ((A.X N i : ℤ) + A.H N l - 1) % A.H N l < A.H N l := by
      simpa [abs_of_pos hHpos] using hremLoLt
    have hremBound : ((A.X N i : ℤ) + A.H N l - 1) % A.H N l ≤ A.H N l - 1 := by omega
    omega
  have hKLo : (A.H N l : ℤ) * (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ≤
      (A.H N l : ℤ) * k := Int.mul_le_mul_of_nonneg_left hk'.1 hHpos.le
  have hHiMul : (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) ≤
      (A.X N i : ℤ) ^ 2 := by
    have hremHi := Int.emod_nonneg ((A.X N i : ℤ) ^ 2) hHne
    have hdivHi := Int.emod_add_mul_ediv ((A.X N i : ℤ) ^ 2) (A.H N l : ℤ)
    omega
  have hkStep : k + 1 ≤ (A.X N i : ℤ) ^ 2 / A.H N l := by omega
  have hKHi : (A.H N l : ℤ) * (k + 1) ≤
      (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) :=
    Int.mul_le_mul_of_nonneg_left hkStep hHpos.le
  constructor
  · calc
      (A.X N i : ℤ) ≤ (A.H N l : ℤ) *
          (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) := hLoMul
      _ ≤ (A.H N l : ℤ) * k := hKLo
      _ = k * (A.H N l : ℤ) := by ring
  · calc
      (k + 1) * (A.H N l : ℤ) = (A.H N l : ℤ) * (k + 1) := by ring
      _ ≤ (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) := hKHi
      _ ≤ (A.X N i : ℤ) ^ 2 := hHiMul

theorem p_g3_cellPoint_bounds {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (hq : 0 < p_g3_cellOrder A N l) (C : ℤ × ℕ)
    (hC : C ∈ p_g3_cells A N i l) (x : ℕ)
    (hx : x < p_g3_cellOrder A N l) :
    (A.X N i : ℤ) ≤ p_g3_cellPoint A N l C x ∧
      p_g3_cellPoint A N l C x < (A.X N i : ℤ) ^ 2 := by
  have hCmem : C.1 ∈ p_g3_fullIntervals A N i l ∧ C.2 < A.M N := by
    simpa [p_g3_cells] using hC
  have hb := p_g3_fullInterval_bounds A N i l C.1 hCmem.1
  have hremLt : (C.2 : ℤ) + (A.M N : ℤ) * x < (A.H N l : ℤ) := by
    have hx1 : x + 1 ≤ p_g3_cellOrder A N l := Nat.succ_le_of_lt hx
    have hsmall : C.2 + A.M N * x < A.M N * (x + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hmul : A.M N * (x + 1) ≤ A.M N * p_g3_cellOrder A N l :=
      Nat.mul_le_mul_left _ hx1
    have hMq : A.M N * p_g3_cellOrder A N l = A.H N l := by
      dsimp [p_g3_cellOrder]
      simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
    exact_mod_cast (hsmall.trans_le (hMq ▸ hmul))
  have hremPos : (0 : ℤ) ≤ (C.2 : ℤ) + (A.M N : ℤ) * x := by positivity
  constructor
  · have hmul := hb.1
    have hpoint : p_g3_cellPoint A N l C x =
        C.1 * (A.H N l : ℤ) + ((C.2 : ℤ) + (A.M N : ℤ) * x) := by
      simp [p_g3_cellPoint]
      ring
    rw [hpoint]
    exact hmul.trans (le_add_of_nonneg_right hremPos)
  · have hpoint : p_g3_cellPoint A N l C x =
        C.1 * (A.H N l : ℤ) + ((C.2 : ℤ) + (A.M N : ℤ) * x) := by
      simp [p_g3_cellPoint]
      ring
    calc
      p_g3_cellPoint A N l C x = C.1 * (A.H N l : ℤ) +
          ((C.2 : ℤ) + (A.M N : ℤ) * x) := hpoint
      _ < C.1 * (A.H N l : ℤ) + (A.H N l : ℤ) := by
        calc
          _ = ((C.2 : ℤ) + (A.M N : ℤ) * x) + C.1 * (A.H N l : ℤ) := by ring
          _ < (A.H N l : ℤ) + C.1 * (A.H N l : ℤ) := by
            have ht := add_lt_add_left hremLt (C.1 * (A.H N l : ℤ))
            nlinarith [ht]
          _ = _ := by ring
      _ = (C.1 + 1) * (A.H N l : ℤ) := by ring
      _ ≤ (A.X N i : ℤ) ^ 2 := hb.2

theorem p_g3_cellPoint_injective {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l) :
    Set.InjOn (fun z : (ℤ × ℕ) × ℕ => p_g3_cellPoint A N l z.1 z.2)
      (↑((p_g3_cells A N i l).product (Finset.range (p_g3_cellOrder A N l))) :
        Set ((ℤ × ℕ) × ℕ)) := by
  intro p hp p' hp' heq
  have hpParts := Finset.mem_product.mp hp
  have hpParts' := Finset.mem_product.mp hp'
  have hpCell : p.1.1 ∈ p_g3_fullIntervals A N i l ∧ p.1.2 < A.M N := by
    simpa [p_g3_cells] using hpParts.1
  have hpCell' : p'.1.1 ∈ p_g3_fullIntervals A N i l ∧ p'.1.2 < A.M N := by
    simpa [p_g3_cells] using hpParts'.1
  have hpX : p.2 < p_g3_cellOrder A N l := Finset.mem_range.mp hpParts.2
  have hpX' : p'.2 < p_g3_cellOrder A N l := Finset.mem_range.mp hpParts'.2
  have hdec := p_g3_point_div_mod A N i l hq p.1 hpParts.1 p.2 hpX
  have hdec' := p_g3_point_div_mod A N i l hq p'.1 hpParts'.1 p'.2 hpX'
  have hk : p.1.1 = p'.1.1 := by
    have h := congrArg (fun z : ℤ => z / (A.H N l : ℤ)) heq
    rw [hdec.1, hdec'.1] at h
    exact h
  have hr : (p.1.2 : ℤ) + (A.M N : ℤ) * p.2 =
      (p'.1.2 : ℤ) + (A.M N : ℤ) * p'.2 := by
    have h := congrArg (fun z : ℤ => z % (A.H N l : ℤ)) heq
    rw [hdec.2, hdec'.2] at h
    exact h
  have hMposInt : 0 < (A.M N : ℤ) := by exact_mod_cast A.Mpos N
  have hmod := congrArg (fun z : ℤ => z % (A.M N : ℤ)) hr
  have hρ : p.1.2 = p'.1.2 := by
    have hmodCast : ((p.1.2 % A.M N : ℕ) : ℤ) =
        ((p'.1.2 % A.M N : ℕ) : ℤ) := by
      simpa only [Int.add_mul_emod_self_left, ← Int.natCast_mod] using hmod
    have hmodNat : p.1.2 % A.M N = p'.1.2 % A.M N := by exact_mod_cast hmodCast
    simpa [Nat.mod_eq_of_lt hpCell.2, Nat.mod_eq_of_lt hpCell'.2] using hmodNat
  have hxmul : (A.M N : ℤ) * p.2 = (A.M N : ℤ) * p'.2 := by
    rw [hρ] at hr
    exact add_left_cancel hr
  have hx : p.2 = p'.2 := by
    have hxInt : (p.2 : ℤ) = (p'.2 : ℤ) := mul_left_cancel₀ hMposInt.ne' hxmul
    exact_mod_cast hxInt
  apply Prod.ext
  · apply Prod.ext
    · exact hk
    · exact_mod_cast hρ
  · exact hx

theorem p_g3_cellMass_sum_image {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l) :
    p_g3_totalCellMass A N i l =
      ∑ z ∈ p_g3_cellPointImage A N i l, mu A N i z := by
  calc
    p_g3_totalCellMass A N i l =
        ∑ p ∈ p_g3_cellPairs A N i l,
          mu A N i (p_g3_cellPoint A N l p.1 p.2) := by
            dsimp [p_g3_totalCellMass, p_g3_cellMass, p_g3_cellPairs]
            rw [Finset.sum_product]
    _ = ∑ z ∈ p_g3_cellPointImage A N i l, mu A N i z := by
          simpa [p_g3_cellPairs, p_g3_cellPointImage] using
            (Finset.sum_image (p_g3_cellPoint_injective A N i l hq)).symm

theorem p_g3_support_decomposition {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (hq : 0 < p_g3_cellOrder A N l) (z : ℤ)
    (hz : z ∈ muSupport A N i)
    (hk : z / (A.H N l : ℤ) ∈ p_g3_fullIntervals A N i l) :
    ∃ C x, C ∈ p_g3_cells A N i l ∧ x < p_g3_cellOrder A N l ∧
      p_g3_cellPoint A N l C x = z := by
  classical
  have hzImage := Finset.mem_image.mp hz
  obtain ⟨n, hn, hzn⟩ := hzImage
  have hzn' : (n : ℤ) = z := hzn
  let r : ℕ := n % A.H N l
  let ρ : ℕ := r % A.M N
  let x : ℕ := r / A.M N
  have hdivCast : ((n / A.H N l : ℕ) : ℤ) = z / (A.H N l : ℤ) := by
    rw [← hzn']
    exact Int.natCast_div _ _
  have hmodCast : ((r : ℕ) : ℤ) = z % (A.H N l : ℤ) := by
    dsimp [r]
    rw [← hzn']
  have hkNat : ((n / A.H N l : ℕ) : ℤ) ∈ p_g3_fullIntervals A N i l := by
    simpa [hdivCast] using hk
  have hρlt : ρ < A.M N := by dsimp [ρ]; exact Nat.mod_lt _ (A.Mpos N)
  have hrlt : r < A.H N l := by dsimp [r]; exact Nat.mod_lt _ (A.Hpos N l)
  have hMq : A.M N * p_g3_cellOrder A N l = A.H N l := by
    dsimp [p_g3_cellOrder]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
  have hxlt : x < p_g3_cellOrder A N l := by
    dsimp [x]
    apply (Nat.div_lt_iff_lt_mul (A.Mpos N)).2
    have hrLt' : r < A.M N * p_g3_cellOrder A N l := by simpa [hMq] using hrlt
    simpa [Nat.mul_comm] using hrLt'
  let C : ℤ × ℕ := ((n / A.H N l : ℕ), ρ)
  have hC : C ∈ p_g3_cells A N i l := by
    exact Finset.mem_product.mpr ⟨hkNat, Finset.mem_range.mpr hρlt⟩
  have hDecompH : (n : ℤ) = (r : ℤ) + (A.H N l : ℤ) * (n / A.H N l : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n (A.H N l)).symm
  have hDecompM : (r : ℤ) = (ρ : ℤ) + (A.M N : ℤ) * x := by
    exact_mod_cast (Nat.mod_add_div r (A.M N)).symm
  have hBase : z = (r : ℤ) + (A.H N l : ℤ) * (z / (A.H N l : ℤ)) := by
    calc
      z = (n : ℤ) := hzn'.symm
      _ = (r : ℤ) + (A.H N l : ℤ) * (n / A.H N l : ℕ) := hDecompH
      _ = (r : ℤ) + (A.H N l : ℤ) * (z / (A.H N l : ℤ)) := by rw [hdivCast]
  have hPointEq : p_g3_cellPoint A N l C x = z := by
    calc
      p_g3_cellPoint A N l C x = C.1 * (A.H N l : ℤ) + (C.2 : ℤ) +
          (A.M N : ℤ) * x := by simp [p_g3_cellPoint, C] <;> ring
      _ = ((n / A.H N l : ℕ) : ℤ) * (A.H N l : ℤ) + (r : ℤ) := by
        dsimp [C]
        omega
      _ = (n : ℤ) := by
        calc
          _ = (r : ℤ) + (A.H N l : ℤ) * (n / A.H N l : ℕ) := by ring
          _ = (n : ℤ) := hDecompH.symm
      _ = z := hzn'
  exact ⟨C, x, hC, hxlt, hPointEq⟩

theorem p_g3_support_core {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (hq : 0 < p_g3_cellOrder A N l) (z : ℤ)
    (hz : z ∈ muSupport A N i)
    (hk : z / (A.H N l : ℤ) ∈ p_g3_fullIntervals A N i l) :
    z ∈ p_g3_cellPointImage A N i l := by
  obtain ⟨C, x, hC, hx, hzx⟩ := p_g3_support_decomposition A N i l hq z hz hk
  exact Finset.mem_image.mpr
    ⟨(C, x), Finset.mem_product.mpr ⟨hC, Finset.mem_range.mpr hx⟩, hzx⟩

theorem p_g3_support_outside {K : ℕ} (A : Parameters K) (N : ℕ) (i l : Fin K)
    (hq : 0 < p_g3_cellOrder A N l) (hHleX : A.H N l ≤ A.X N i)
    (z : ℤ) (hz : z ∈ muSupport A N i)
    (hzn : z ∉ p_g3_cellPointImage A N i l) :
    z ∈ p_g3_partialIntervals A N i l := by
  classical
  obtain ⟨n, hn, hznat⟩ := Finset.mem_image.mp hz
  have hznat' : (n : ℤ) = z := hznat
  have hnrange := Finset.mem_filter.mp hn
  have hIcoNat := Finset.mem_Ico.mp hnrange.1
  have hIco : (A.X N i : ℤ) ≤ z ∧ z < (A.X N i : ℤ) ^ 2 := by
    constructor
    · rw [← hznat']
      exact_mod_cast hIcoNat.1
    · rw [← hznat']
      exact_mod_cast hIcoNat.2
  let k : ℤ := z / (A.H N l : ℤ)
  let r : ℤ := z % (A.H N l : ℤ)
  have hHpos : 0 < (A.H N l : ℤ) := by exact_mod_cast A.Hpos N l
  have hHne : (A.H N l : ℤ) ≠ 0 := hHpos.ne'
  have hr0 : 0 ≤ r := by dsimp [r]; exact Int.emod_nonneg _ hHne
  have hrlt : r < (A.H N l : ℤ) := by
    dsimp [r]
    simpa [abs_of_pos hHpos] using Int.emod_lt_abs z hHne
  have hdecomp : r + (A.H N l : ℤ) * k = z := by
    dsimp [r, k]
    exact Int.emod_add_mul_ediv z (A.H N l : ℤ)
  have hknot : k ∉ p_g3_fullIntervals A N i l := by
    intro hk
    exact hzn (p_g3_support_core A N i l hq z hz (by simpa [k] using hk))
  have hkcase : k < (((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ∨
      ((A.X N i : ℤ) ^ 2 / A.H N l) ≤ k := by
    have hnotBounds : ¬ ((((A.X N i : ℤ) + A.H N l - 1) / A.H N l) ≤ k ∧
        k < ((A.X N i : ℤ) ^ 2 / A.H N l)) := by
      intro h
      exact hknot (Finset.mem_Ico.mpr h)
    omega
  rcases hkcase with hlo | hhi
  · have hk1 : k + 1 ≤ ((A.X N i : ℤ) + A.H N l - 1) / A.H N l := by omega
    have hmul : (A.H N l : ℤ) * (k + 1) ≤ (A.X N i : ℤ) + A.H N l - 1 := by
      simpa [mul_comm] using (Int.le_ediv_iff_mul_le hHpos).mp hk1
    have hzlt : z < (A.X N i : ℤ) + A.H N l := by
      calc
        z = r + (A.H N l : ℤ) * k := hdecomp.symm
        _ < (A.H N l : ℤ) * (k + 1) := by nlinarith [hrlt]
        _ ≤ (A.X N i : ℤ) + A.H N l - 1 := hmul
        _ < (A.X N i : ℤ) + A.H N l := by omega
    exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨hIco.1, hzlt⟩)
  · have hremHi := Int.emod_nonneg ((A.X N i : ℤ) ^ 2) hHne
    have hremHiLt := Int.emod_lt_abs ((A.X N i : ℤ) ^ 2) hHne
    have hdivHi := Int.emod_add_mul_ediv ((A.X N i : ℤ) ^ 2) (A.H N l : ℤ)
    have hHiMul : (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) ≤
        (A.X N i : ℤ) ^ 2 := by omega
    have hHiLower : (A.X N i : ℤ) ^ 2 - A.H N l <
        (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) := by
      have hremHiLt' : ((A.X N i : ℤ) ^ 2 % A.H N l) < (A.H N l : ℤ) := by
        simpa [abs_of_pos hHpos] using hremHiLt
      omega
    have hkMul : (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) ≤
        (A.H N l : ℤ) * k := Int.mul_le_mul_of_nonneg_left hhi hHpos.le
    have hzge : (A.X N i : ℤ) ^ 2 - A.H N l < z := by
      have hHkLeZ : (A.H N l : ℤ) * k ≤ z := by
        rw [← hdecomp]
        exact le_add_of_nonneg_left hr0
      calc
        _ < (A.H N l : ℤ) * ((A.X N i : ℤ) ^ 2 / A.H N l) := hHiLower
        _ ≤ (A.H N l : ℤ) * k := hkMul
        _ ≤ z := hHkLeZ
    have hHleXsq : A.H N l ≤ (A.X N i) ^ 2 := by nlinarith [hHleX]
    have hbelow : (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ) < z := by
      simpa [Int.natCast_sub hHleXsq] using hzge
    exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_of_lt hbelow, hIco.2⟩)

theorem p_g3_partialIntervals_card {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hHleX : A.H N l ≤ A.X N i) :
    (p_g3_partialIntervals A N i l).card ≤ 2 * A.H N l := by
  have hXiPos : 0 < A.X N i := A.Xpos N i
  have hHleXsq : A.H N l ≤ (A.X N i) ^ 2 := by nlinarith [hHleX]
  have hStartLe : (A.X N i : ℤ) ≤ ((A.X N i + A.H N l : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_add_right (A.X N i) (A.H N l)
  have hStartCardZ :
      ((Finset.Ico (A.X N i : ℤ) ((A.X N i + A.H N l : ℕ) : ℤ)).card : ℤ) =
        (A.H N l : ℤ) := by
    rw [Int.card_Ico_of_le (A.X N i : ℤ) ((A.X N i + A.H N l : ℕ) : ℤ) hStartLe]
    push_cast
    ring
  have hStartCard : Finset.card
      (Finset.Ico (A.X N i : ℤ) ((A.X N i + A.H N l : ℕ) : ℤ)) = A.H N l := by
    exact_mod_cast hStartCardZ
  have hEndLo : (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ) ≤ ((A.X N i) ^ 2 : ℤ) := by
    exact_mod_cast Nat.sub_le _ _
  have hEndCardZ :
      ((Finset.Ico (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ)
        ((A.X N i) ^ 2 : ℤ)).card : ℤ) = (A.H N l : ℤ) := by
    rw [Int.card_Ico_of_le (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ)
      ((A.X N i) ^ 2 : ℤ) hEndLo]
    rw [Int.natCast_sub hHleXsq]
    simp
  have hEndCard : Finset.card
      (Finset.Ico (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ) ((A.X N i) ^ 2 : ℤ)) =
        A.H N l := by exact_mod_cast hEndCardZ
  dsimp [p_g3_partialIntervals]
  calc
    _ ≤ (Finset.Ico (A.X N i : ℤ) ((A.X N i + A.H N l : ℕ) : ℤ)).card +
        (Finset.Ico (((A.X N i) ^ 2 - A.H N l : ℕ) : ℤ)
          ((A.X N i) ^ 2 : ℤ)).card := Finset.card_union_le _ _
    _ = A.H N l + A.H N l := by rw [hStartCard, hEndCard]
    _ = 2 * A.H N l := by omega

theorem p_g3_partial_mass_bound {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l)
    (hcut : 4 * primorial (N + 1) ≤ A.X N i)
    (hHleX : A.H N l ≤ A.X N i) :
    (∑ z ∈ (muSupport A N i \ p_g3_cellPointImage A N i l), mu A N i z) ≤
      8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) / (A.X N i : ℝ) := by
  classical
  let X := A.X N i
  let W := primorial (N + 1)
  let H := A.H N l
  have hXpos : 0 < X := A.Xpos N i
  have hWpos : 0 < W := primorial_pos _
  have hHnorm : 0 < harmonicNormalizer X W := by
    have hm := OAI.RawHarmonicProbability.mass_pos X W hWpos hcut
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using hm
  have hNormEq : harmonicNormalizer X W =
      OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
    simp [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, Nat.coprime_comm]
  have hNormLower : (1 : ℝ) / (4 * W) ≤ harmonicNormalizer X W := by
    have hraw := OAI.DyadicHarmonicBoundary.dyadic_lower X W hWpos hcut
    have hXX : X + X ≤ X ^ 2 := by
      have hX4 : 4 ≤ X := by omega
      nlinarith
    have htotient : (1 : ℝ) ≤ (Nat.totient W : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hWpos).ne')
    rw [hNormEq]
    have hraw' := hraw.trans (OAI.DyadicHarmonicBoundary.mass_mono hXX)
    exact (div_le_div_of_nonneg_right htotient (by positivity)).trans hraw'
  have hNormPos : 0 < harmonicNormalizer X W := lt_of_lt_of_le (by positivity) hNormLower
  have hsubset : muSupport A N i \ p_g3_cellPointImage A N i l ⊆
      p_g3_partialIntervals A N i l ∩ muSupport A N i := by
    intro z hz
    have hzSupport := (Finset.mem_sdiff.mp hz).1
    have hnotImage := (Finset.mem_sdiff.mp hz).2
    have hout := p_g3_support_outside A N i l hq hHleX z hzSupport hnotImage
    exact Finset.mem_inter.mpr ⟨hout, hzSupport⟩
  have hpointBound (z : ℤ) (hz : z ∈ muSupport A N i) :
      mu A N i z ≤ (4 * (W : ℝ)) / (X : ℝ) := by
    obtain ⟨n, hn, hzn⟩ := Finset.mem_image.mp hz
    have hzn' : (n : ℤ) = z := hzn
    have hnrange := Finset.mem_filter.mp hn
    have hIco := Finset.mem_Ico.mp hnrange.1
    have hnatpos : 0 < n := lt_of_lt_of_le (by exact_mod_cast hXpos) hIco.1
    have hpoint : mu A N i (n : ℤ) =
        1 / ((n : ℝ) * harmonicNormalizer X W) := by
      change harmonicLaw X W (n : ℤ) = _
      have htn : Int.toNat (n : ℤ) = n := Int.toNat_natCast n
      have hvalid : 0 ≤ (n : ℤ) ∧ X ≤ Int.toNat (n : ℤ) ∧
          Int.toNat (n : ℤ) < X ^ 2 ∧ Nat.Coprime (Int.toNat (n : ℤ)) W := by
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · simpa [htn, X] using hIco.1
        · simpa [htn, X] using hIco.2
        · simpa [htn, W] using hnrange.2
      unfold harmonicLaw
      rw [if_pos hvalid]
      rw [htn]
    rw [← hzn', hpoint]
    have hXcast : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
    have hWcast : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
    have hnX : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hIco.1
    have hden : (X : ℝ) / (4 * (W : ℝ)) ≤
        (n : ℝ) * harmonicNormalizer X W := by
      calc
        (X : ℝ) / (4 * (W : ℝ)) = (X : ℝ) * (1 / (4 * (W : ℝ))) := by ring
        _ ≤ (X : ℝ) * harmonicNormalizer X W :=
          mul_le_mul_of_nonneg_left hNormLower (by positivity)
        _ ≤ (n : ℝ) * harmonicNormalizer X W :=
          mul_le_mul_of_nonneg_right hnX hNormPos.le
    have hsmall : 0 < (X : ℝ) / (4 * (W : ℝ)) := by positivity
    calc
      _ ≤ ((X : ℝ) / (4 * (W : ℝ)))⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hsmall hden
      _ = (4 * (W : ℝ)) / (X : ℝ) := by field_simp
  have hsumSupport :
      (∑ z ∈ (muSupport A N i \ p_g3_cellPointImage A N i l), mu A N i z) ≤
        ∑ z ∈ p_g3_partialIntervals A N i l ∩ muSupport A N i, mu A N i z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro z hz hnot
    exact mu_nonneg A N i z
  have hsumBound :
      (∑ z ∈ p_g3_partialIntervals A N i l ∩ muSupport A N i, mu A N i z) ≤
        ∑ z ∈ p_g3_partialIntervals A N i l ∩ muSupport A N i,
          (4 * (W : ℝ)) / (X : ℝ) := by
    apply Finset.sum_le_sum
    intro z hz
    exact hpointBound z (Finset.mem_inter.mp hz).2
  calc
    _ ≤ ∑ z ∈ p_g3_partialIntervals A N i l ∩ muSupport A N i, mu A N i z := hsumSupport
    _ ≤ ∑ z ∈ p_g3_partialIntervals A N i l ∩ muSupport A N i,
        (4 * (W : ℝ)) / (X : ℝ) := hsumBound
    _ = ((p_g3_partialIntervals A N i l ∩ muSupport A N i).card : ℝ) *
        ((4 * (W : ℝ)) / (X : ℝ)) := by simp [Finset.sum_const]
    _ ≤ (2 * (H : ℝ)) * ((4 * (W : ℝ)) / (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (le_trans (Finset.card_mono Finset.inter_subset_left)
        (p_g3_partialIntervals_card A N i l hHleX))
    _ = 8 * (H : ℝ) * (W : ℝ) / (X : ℝ) := by ring

private theorem p_g3_mu_zero_of_not_support {K : ℕ} (A : Parameters K) (N : ℕ)
    (i : Fin K) (z : ℤ) (hz : z ∉ muSupport A N i) : mu A N i z = 0 := by
  by_cases hz0 : 0 ≤ z
  · have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
    unfold mu harmonicLaw
    split_ifs with h
    · apply False.elim
      apply hz
      unfold muSupport
      apply Finset.mem_image.mpr
      refine ⟨z.toNat, Finset.mem_filter.mpr ?_, hzNat⟩
      refine ⟨Finset.mem_Ico.mpr ?_, h.2.2.2⟩
      constructor
      · exact h.2.1
      · exact h.2.2.1
    · rfl
  · simp [mu, harmonicLaw, hz0]

theorem p_g3_Emu_eq_sum_on_finite_set {K : ℕ} (A : Parameters K) (N : ℕ)
    (i : Fin K) (S : Finset ℤ) (f : ℤ → ℝ)
    (hzero : ∀ z ∈ muSupport A N i, z ∉ S → f z = 0) :
    Emu A N i f = ∑ z ∈ S, mu A N i z * f z := by
  classical
  rw [Emu_eq_sum_support]
  have hleft :
      (∑ z ∈ muSupport A N i, mu A N i z * f z) =
        ∑ z ∈ muSupport A N i ∩ S, mu A N i z * f z := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hz hnot
    have hnotS : z ∉ S := by
      intro hzS
      exact hnot (Finset.mem_inter.mpr ⟨hz, hzS⟩)
    rw [hzero z hz hnotS]
    simp
  have hright :
      (∑ z ∈ muSupport A N i ∩ S, mu A N i z * f z) =
        ∑ z ∈ S, mu A N i z * f z := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro z hz hnot
    have hnotSupport : z ∉ muSupport A N i := by
      intro hzSupport
      exact hnot (Finset.mem_inter.mpr ⟨hzSupport, hz⟩)
    rw [p_g3_mu_zero_of_not_support A N i z hnotSupport]
    simp
  exact hleft.trans hright

theorem p_g3_sum_image_cells {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l)
    (Good : Finset (ℤ × ℕ)) (hGood : Good ⊆ p_g3_cells A N i l)
    (f : ℤ → ℝ) :
    (∑ z ∈ ((Good.product (Finset.range (p_g3_cellOrder A N l))).image
        (fun p : (ℤ × ℕ) × ℕ => p_g3_cellPoint A N l p.1 p.2)), f z) =
      ∑ C ∈ Good, ∑ x ∈ Finset.range (p_g3_cellOrder A N l),
        f (p_g3_cellPoint A N l C x) := by
  classical
  let pairs := Good.product (Finset.range (p_g3_cellOrder A N l))
  let point := fun p : (ℤ × ℕ) × ℕ => p_g3_cellPoint A N l p.1 p.2
  have hinj : Set.InjOn point (↑pairs : Set ((ℤ × ℕ) × ℕ)) := by
    intro p hp p' hp' heq
    have hpParts := Finset.mem_product.mp hp
    have hpParts' := Finset.mem_product.mp hp'
    have hpAll : p.1 ∈ p_g3_cells A N i l := hGood hpParts.1
    have hpAll' : p'.1 ∈ p_g3_cells A N i l := hGood hpParts'.1
    exact p_g3_cellPoint_injective A N i l hq
      (Finset.mem_product.mpr ⟨hpAll, hpParts.2⟩)
      (Finset.mem_product.mpr ⟨hpAll', hpParts'.2⟩) heq
  calc
    _ = ∑ p ∈ pairs, f (point p) := by
      simpa [pairs, point] using (Finset.sum_image hinj)
    _ = ∑ C ∈ Good, ∑ x ∈ Finset.range (p_g3_cellOrder A N l),
        f (p_g3_cellPoint A N l C x) := by
      dsimp [pairs, point]
      rw [Finset.sum_product]

theorem p_g3_Emu_mass_eq_one {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (hcut : 4 * primorial (N + 1) ≤ A.X N i) :
    Emu A N i (fun _ => 1) = 1 := by
  classical
  let T := (Finset.Ico (A.X N i) ((A.X N i) ^ 2)).filter
    (fun n => Nat.Coprime n (primorial (N + 1)))
  let Z := harmonicNormalizer (A.X N i) (primorial (N + 1))
  have hZ : 0 < Z := by
    have hm := OAI.RawHarmonicProbability.mass_pos (A.X N i) (primorial (N + 1))
      (primorial_pos _) hcut
    simpa [Z, harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using hm
  rw [Emu_eq_sum_support]
  change (∑ y ∈ Finset.image (fun n : ℕ => (n : ℤ)) T,
      mu A N i y * 1) = 1
  rw [Finset.sum_image Nat.cast_injective.injOn]
  calc
    (∑ n ∈ T, mu A N i (n : ℤ) * 1) =
        ∑ n ∈ T, 1 / ((n : ℝ) * Z) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      have hIco := Finset.mem_Ico.mp hmem.1
      have hvalid : 0 ≤ (n : ℤ) ∧ A.X N i ≤ Int.toNat (n : ℤ) ∧
          Int.toNat (n : ℤ) < (A.X N i) ^ 2 ∧
            Nat.Coprime (Int.toNat (n : ℤ)) (primorial (N + 1)) := by
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · simpa only [Int.toNat_natCast] using hIco.1
        · simpa only [Int.toNat_natCast] using hIco.2
        · simpa only [Int.toNat_natCast] using hmem.2
      simp only [mu, harmonicLaw]
      rw [if_pos hvalid]
      simp [Z, Int.toNat_natCast]
    _ = ∑ n ∈ T, (1 / (n : ℝ)) / Z := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        1 / ((n : ℝ) * Z) = (n : ℝ)⁻¹ * Z⁻¹ := by
          rw [one_div, mul_inv_rev]
          ring
        _ = (1 / (n : ℝ)) / Z := by simp [one_div, div_eq_mul_inv, mul_comm]
    _ = (∑ n ∈ T, 1 / (n : ℝ)) / Z := by rw [Finset.sum_div]
    _ = Z / Z := by simp [Z, T, harmonicNormalizer]
    _ = 1 := div_self (ne_of_gt hZ)

theorem p_g3_totalCellMass_add_tail {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l)
    (hcut : 4 * primorial (N + 1) ≤ A.X N i)
    (hHleX : A.H N l ≤ A.X N i) :
    p_g3_totalCellMass A N i l +
      ∑ z ∈ (muSupport A N i \ p_g3_cellPointImage A N i l), mu A N i z = 1 := by
  classical
  have hImageSupport :
      (∑ z ∈ p_g3_cellPointImage A N i l, mu A N i z) =
        ∑ z ∈ muSupport A N i ∩ p_g3_cellPointImage A N i l, mu A N i z := by
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro z hz hnot
    exact p_g3_mu_zero_of_not_support A N i z (by
      intro hzS
      exact hnot (Finset.mem_inter.mpr ⟨hzS, hz⟩))
  have hUnion : muSupport A N i =
      (muSupport A N i ∩ p_g3_cellPointImage A N i l) ∪
        (muSupport A N i \ p_g3_cellPointImage A N i l) := by
    ext z
    by_cases hz : z ∈ p_g3_cellPointImage A N i l <;> simp [hz]
  have hdisj : Disjoint
      (muSupport A N i ∩ p_g3_cellPointImage A N i l)
      (muSupport A N i \ p_g3_cellPointImage A N i l) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_inter.mp hz).2
  have hEmu := p_g3_Emu_mass_eq_one A N i hcut
  rw [Emu_eq_sum_support] at hEmu
  simp only [mul_one] at hEmu
  rw [hUnion, Finset.sum_union hdisj] at hEmu
  rw [← hImageSupport, ← p_g3_cellMass_sum_image A N i l hq] at hEmu
  simpa [p_g3_totalCellMass] using hEmu

theorem p_g3_totalCellMass_lower {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l)
    (hcut : 4 * primorial (N + 1) ≤ A.X N i)
    (hHleX : A.H N l ≤ A.X N i) :
    1 - 8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) / (A.X N i : ℝ) ≤
      p_g3_totalCellMass A N i l := by
  have hsum := p_g3_totalCellMass_add_tail A N i l hq hcut hHleX
  have htail := p_g3_partial_mass_bound A N i l hq hcut hHleX
  linarith

theorem p_g3_Hsq_over_X_tendsto {K : ℕ} (A : Parameters K) (i l : Fin K)
    (hli : l < i) :
    Tendsto (fun N => (A.H N l : ℝ) ^ 2 / (A.X N i : ℝ)) atTop (𝓝 0) := by
  let XL : ℕ → ℕ := fun N => A.X N l
  let Xi : ℕ → ℕ := fun N => A.X N i
  let H : ℕ → ℕ := fun N => A.H N l
  have hXL : Tendsto XL atTop atTop := by simpa [XL] using A.Xtendsto l
  have hXLReal : Tendsto (fun N => (XL N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hXL
  have hlogDiv : Tendsto (fun N => Real.log (XL N : ℝ) / (XL N : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hXLReal)
  have hHlog : ∀ᶠ N in atTop, (H N : ℝ) ≤ Real.log (XL N : ℝ) := by
    have hdom := A.Xdom l 1 (by norm_num)
    filter_upwards [hdom.eventually_gt_atTop 1] with N hN
    have hHpos : 0 < (H N : ℝ) := by exact_mod_cast A.Hpos N l
    have hratio : (1 : ℝ) < Real.log (XL N : ℝ) / (H N : ℝ) := by
      simpa [XL, H, pow_one] using hN
    have hmul := (lt_div_iff₀ hHpos).mp hratio
    linarith
  have hXorder : ∀ᶠ N in atTop, (Xi N : ℝ) > (XL N : ℝ) ^ 2 := by
    have hdom := HindmanSumsProducts.Parameters.eventually_X_dominates_earlier_square
      A i 1 (by norm_num)
    filter_upwards [hdom] with N hN
    have hprev : (XL N : ℝ) ≤
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) := by
      have hprevNat : A.X N l ≤ OAI.SourceAdmissible.previous (A.X N) i := by
        dsimp [OAI.SourceAdmissible.previous]
        apply Finset.single_le_prod
        · intro j hj
          exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (A.Xpos N j))
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hli⟩
      exact_mod_cast hprevNat
    have hM : (1 : ℝ) ≤ A.M N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (A.Mpos N).ne'
    have hprevSq : (XL N : ℝ) ^ 2 ≤
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hprev 2
    have hMmul : (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 ≤
        (A.M N : ℝ) * (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by
      calc
        _ = 1 * (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    have hscale : (A.M N : ℝ) *
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ^ 2 < (Xi N : ℝ) := by
      simpa [Xi] using hN
    exact hprevSq.trans_lt (hMmul.trans_lt hscale)
  have hlogSq : Tendsto
      (fun N => (Real.log (XL N : ℝ) / (XL N : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using hlogDiv.pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlogSq
  · filter_upwards [Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hXi
    positivity
  · filter_upwards [hHlog, hXorder, hXL.eventually_gt_atTop 1,
      Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hH hX hXLpos hXipos
    have hHpos : 0 ≤ (H N : ℝ) := by positivity
    have hHupper : (H N : ℝ) ^ 2 ≤ (Real.log (XL N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hHpos hH 2
    have hXLposR : (0 : ℝ) < (XL N : ℝ) := by exact_mod_cast (show 0 < XL N by omega)
    have hden : 0 < (XL N : ℝ) ^ 2 := pow_pos hXLposR _
    have hXiLower : (XL N : ℝ) ^ 2 ≤ (Xi N : ℝ) := le_of_lt hX
    have hquot : (H N : ℝ) ^ 2 / (Xi N : ℝ) ≤
        (Real.log (XL N : ℝ)) ^ 2 / (XL N : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (by exact_mod_cast A.Xpos N i) hden).2
      calc
        (H N : ℝ) ^ 2 * (XL N : ℝ) ^ 2 ≤
            (Real.log (XL N : ℝ)) ^ 2 * (XL N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hHupper (sq_nonneg _)
        _ ≤ (Real.log (XL N : ℝ)) ^ 2 * (Xi N : ℝ) :=
          mul_le_mul_of_nonneg_left hXiLower (sq_nonneg _)
    have hratio : (Real.log (XL N : ℝ)) ^ 2 / (XL N : ℝ) ^ 2 =
        (Real.log (XL N : ℝ) / (XL N : ℝ)) ^ 2 := by field_simp
    exact hquot.trans_eq hratio

theorem p_g3_cellError_tendsto {K : ℕ} (A : Parameters K) (i l : Fin K)
    (hli : l < i) :
    Tendsto (fun N => 8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) /
      (A.X N i : ℝ)) atTop (𝓝 0) := by
  have hrate := p_g3_Hsq_over_X_tendsto A i l hli
  have hrate8 : Tendsto (fun N => 8 * (A.H N l : ℝ) ^ 2 /
      (A.X N i : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using hrate.const_mul 8
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate8
  · filter_upwards [Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hX
    positivity
  · filter_upwards [Filter.Eventually.of_forall (fun N => A.Xpos N i)] with N hX
    have hWleH : primorial (N + 1) ≤ A.H N l :=
      (A.Wle N).trans (Nat.le_of_dvd (A.Hpos N l) (A.Hdiv N l))
    have hHnonneg : (0 : ℝ) ≤ A.H N l := by positivity
    have hle : (A.H N l : ℝ) * (primorial (N + 1) : ℝ) ≤
        (A.H N l : ℝ) ^ 2 := by
      calc
        _ ≤ (A.H N l : ℝ) * (A.H N l : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hWleH) hHnonneg
        _ = _ := by ring
    have hdiv := div_le_div_of_nonneg_right hle (by positivity : 0 ≤ (A.X N i : ℝ))
    calc
      8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) / (A.X N i : ℝ) =
          8 * ((A.H N l : ℝ) * (primorial (N + 1) : ℝ) / (A.X N i : ℝ)) := by ring
      _ ≤ 8 * ((A.H N l : ℝ) ^ 2 / (A.X N i : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 8 * (A.H N l : ℝ) ^ 2 / (A.X N i : ℝ) := by ring

private theorem p_g3_reciprocalWeights_uniformTV {ι : Type*} [Fintype ι] [Nonempty ι]
    (base width : ℝ) (hbase : 0 < base) (hwidth : 0 ≤ width)
    (y : ι → ℝ) (hy : ∀ i, base ≤ y i ∧ y i ≤ base + width) :
    ∑ i, |(y i)⁻¹ / (∑ j, (y j)⁻¹) - (Fintype.card ι : ℝ)⁻¹| ≤ width / base := by
  classical
  let lo : ℝ := (base + width)⁻¹
  let hi : ℝ := base⁻¹
  let S : ℝ := ∑ i, (y i)⁻¹
  have hbw : 0 < base + width := by linarith
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hhi : 0 < hi := by dsimp [hi]; positivity
  have hypos (i : ι) : 0 < y i := lt_of_lt_of_le hbase (hy i).1
  have hwi_lo (i : ι) : lo ≤ (y i)⁻¹ := by
    dsimp [lo]
    simpa [one_div] using one_div_le_one_div_of_le (hypos i) (hy i).2
  have hwi_hi (i : ι) : (y i)⁻¹ ≤ hi := by
    dsimp [hi]
    simpa [one_div] using one_div_le_one_div_of_le hbase (hy i).1
  have hSpos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (hypos i)) Finset.univ_nonempty
  have hcardpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hSlo : (Fintype.card ι : ℝ) * lo ≤ S := by
    dsimp [S]
    calc
      _ = ∑ i, lo := by simp [Finset.sum_const, Fintype.card_ne_zero]
      _ ≤ ∑ i, (y i)⁻¹ := Finset.sum_le_sum fun i _ => hwi_lo i
  have hmean_lo : lo ≤ S / Fintype.card ι := by
    rw [le_div_iff₀ hcardpos]
    simpa [mul_comm] using hSlo
  have hmean_hi : S / Fintype.card ι ≤ hi := by
    rw [div_le_iff₀ hcardpos]
    calc
      S = ∑ i, (y i)⁻¹ := rfl
      _ ≤ ∑ i, hi := Finset.sum_le_sum fun i _ => hwi_hi i
      _ = hi * (Fintype.card ι : ℝ) := by
        simpa [Finset.sum_const, Fintype.card_ne_zero, mul_comm]
  have hgap : 0 ≤ hi - lo := sub_nonneg.mpr (by
    dsimp [hi, lo]
    simpa [one_div] using
      one_div_le_one_div_of_le hbase (le_add_of_nonneg_right hwidth))
  have hterm (i : ι) :
      |(y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹| ≤ (hi - lo) / S := by
    have hdiff : |(y i)⁻¹ - S / Fintype.card ι| ≤ hi - lo := by
      rw [abs_le]
      constructor <;> linarith [hwi_lo i, hwi_hi i, hmean_lo, hmean_hi]
    have hrewrite : (y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹ =
        ((y i)⁻¹ - S / Fintype.card ι) / S := by
      field_simp [ne_of_gt hSpos, ne_of_gt hcardpos]
    rw [hrewrite, abs_div, abs_of_pos hSpos]
    exact div_le_div_of_nonneg_right hdiff hSpos.le
  have hcardRatio : (Fintype.card ι : ℝ) / S ≤ lo⁻¹ := by
    apply (div_le_iff₀ hSpos).2
    have := (le_div_iff₀ hlo).2 hSlo
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    _ ≤ ∑ _i : ι, ((hi - lo) / S) := Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * ((hi - lo) / S) := by simp
    _ = (hi - lo) * ((Fintype.card ι : ℝ) / S) := by ring
    _ ≤ (hi - lo) * lo⁻¹ := mul_le_mul_of_nonneg_left hcardRatio hgap
    _ = width / base := by
      dsimp [hi, lo]
      field_simp [ne_of_gt hbase, ne_of_gt hbw]
      ring

theorem p_g3_reciprocalWeights_uniform_expect_diff {ι : Type*} [Fintype ι] [Nonempty ι]
    (base width : ℝ) (hbase : 0 < base) (hwidth : 0 ≤ width)
    (y g : ι → ℝ) (hy : ∀ i, base ≤ y i ∧ y i ≤ base + width)
    (hg : ∀ i, |g i| ≤ 1) :
    |(∑ i, (y i)⁻¹ * g i) / (∑ i, (y i)⁻¹) -
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, g i| ≤ width / base := by
  classical
  have hTV := p_g3_reciprocalWeights_uniformTV base width hbase hwidth y hy
  let S : ℝ := ∑ i, (y i)⁻¹
  have hSpos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (lt_of_lt_of_le hbase (hy i).1))
      Finset.univ_nonempty
  have hsum1 :
      (∑ i, (y i)⁻¹ * g i) / S = ∑ i, ((y i)⁻¹ / S) * g i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsum2 : (Fintype.card ι : ℝ)⁻¹ * ∑ i, g i =
      ∑ i, (Fintype.card ι : ℝ)⁻¹ * g i := by rw [Finset.mul_sum]
  rw [hsum1, hsum2, ← Finset.sum_sub_distrib]
  have hsum3 :
      (∑ i, ((y i)⁻¹ / S * g i - (Fintype.card ι : ℝ)⁻¹ * g i)) =
        ∑ i, ((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum3]
  calc
    |∑ i, ((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i| ≤
        ∑ i, |((y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹) * g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(y i)⁻¹ / S - (Fintype.card ι : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hg i) (abs_nonneg _)
    _ ≤ width / base := hTV

theorem p_g3_cellExpectationCompare {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l)
    (hcut : 4 * primorial (N + 1) ≤ A.X N i)
    (C : ℤ × ℕ) (hC : C ∈ p_g3_cells A N i l)
    (g : ℕ → ℝ) (hg : ∀ x < p_g3_cellOrder A N l, |g x| ≤ 1) :
    |(∑ x ∈ Finset.range (p_g3_cellOrder A N l),
        mu A N i (p_g3_cellPoint A N l C x) * g x) -
      p_g3_cellMass A N i l C *
        ((p_g3_cellOrder A N l : ℝ)⁻¹ *
          ∑ x ∈ Finset.range (p_g3_cellOrder A N l), g x)| ≤
        p_g3_cellMass A N i l C * ((A.H N l : ℝ) / (A.X N i : ℝ)) := by
  classical
  let q := p_g3_cellOrder A N l
  let X := A.X N i
  let W := primorial (N + 1)
  let H := A.H N l
  let M := A.M N
  let baseInt : ℤ := C.1 * (H : ℤ) + (C.2 : ℤ)
  let base : ℕ := baseInt.toNat
  have hCmem : C.1 ∈ p_g3_fullIntervals A N i l ∧ C.2 < M := by
    simpa [p_g3_cells, M] using hC
  have hb := p_g3_fullInterval_bounds A N i l C.1 hCmem.1
  have hXiInt : 0 < (X : ℤ) := by exact_mod_cast A.Xpos N i
  have hC1nonneg : 0 ≤ C.1 := by
    have hXile : (0 : ℤ) ≤ (X : ℤ) := le_of_lt hXiInt
    have hC1mul : 0 ≤ C.1 * (H : ℤ) := le_trans hXile hb.1
    nlinarith
  have hbaseIntNonneg : 0 ≤ baseInt := by
    dsimp [baseInt]
    positivity
  have hbaseCast : (base : ℤ) = baseInt := by
    simp [base, Int.toNat_of_nonneg hbaseIntNonneg]
  have hbaseLower : (X : ℝ) ≤ (base : ℝ) := by
    have hLowerInt : (X : ℤ) ≤ baseInt := by
      dsimp [baseInt]
      have hρ : (0 : ℤ) ≤ (C.2 : ℤ) := by positivity
      nlinarith
    have hLowerInt' : (X : ℤ) ≤ (base : ℤ) := by rw [hbaseCast]; exact hLowerInt
    have hLowerNat : X ≤ base := by exact_mod_cast hLowerInt'
    exact_mod_cast hLowerNat
  have hbasePos : 0 < (base : ℝ) := lt_of_lt_of_le (by exact_mod_cast A.Xpos N i) hbaseLower
  have hnormPos : 0 < harmonicNormalizer X W := by
    have hm := OAI.RawHarmonicProbability.mass_pos X W (primorial_pos _) hcut
    simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, one_div, Nat.coprime_comm] using hm
  have hqM : M * q = H := by
    dsimp [M, q, p_g3_cellOrder]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
  have hrootCast (x : ℕ) (hx : x < q) :
      (base + M * x : ℕ) = (p_g3_cellPoint A N l C x).toNat := by
    have hbnds := p_g3_cellPoint_bounds A N i l hq C hC x (by simpa [q] using hx)
    have hpointNonneg : 0 ≤ p_g3_cellPoint A N l C x :=
      le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
    have hrootInt : p_g3_cellPoint A N l C x = baseInt + (M : ℤ) * x := by
      simp [p_g3_cellPoint, baseInt, M, H] <;> ring
    have hcastEq : ((base + M * x : ℕ) : ℤ) = p_g3_cellPoint A N l C x := by
      rw [Nat.cast_add, Nat.cast_mul, hbaseCast, hrootInt]
    exact Int.natCast_inj.mp
      (hcastEq.trans (Int.toNat_of_nonneg hpointNonneg).symm)
  have hWM : W ∣ M := A.Wdiv N
  have hWdiv (x : ℕ) : W ∣ M * x := dvd_mul_of_dvd_left hWM x
  have hcop (x : ℕ) : Nat.Coprime (base + M * x) W ↔ Nat.Coprime base W := by
    obtain ⟨k, hk⟩ := hWdiv x
    rw [hk, Nat.coprime_add_mul_left_left]
  have hpointFormula (x : ℕ) (hx : x < q) (hc : Nat.Coprime base W) :
      mu A N i (p_g3_cellPoint A N l C x) =
        1 / ((base + M * x : ℕ) * harmonicNormalizer X W) := by
    have hbnds := p_g3_cellPoint_bounds A N i l hq C hC x (by simpa [q] using hx)
    have hpointNonneg : 0 ≤ p_g3_cellPoint A N l C x :=
      le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
    have hnatlo : X ≤ (p_g3_cellPoint A N l C x).toNat := by
      have hnatloInt : (X : ℤ) ≤ ((p_g3_cellPoint A N l C x).toNat : ℤ) := by
        simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.1
      exact_mod_cast hnatloInt
    have hnathi : (p_g3_cellPoint A N l C x).toNat < X ^ 2 := by
      have hnathiInt : ((p_g3_cellPoint A N l C x).toNat : ℤ) < (X : ℤ) ^ 2 := by
        simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.2
      exact_mod_cast hnathiInt
    have hcopPoint : Nat.Coprime (p_g3_cellPoint A N l C x).toNat W := by
      rw [← hrootCast x hx]
      exact (hcop x).2 hc
    change harmonicLaw X W (p_g3_cellPoint A N l C x) = _
    have hvalid : 0 ≤ p_g3_cellPoint A N l C x ∧
        X ≤ (p_g3_cellPoint A N l C x).toNat ∧
        (p_g3_cellPoint A N l C x).toNat < X ^ 2 ∧
        Nat.Coprime (p_g3_cellPoint A N l C x).toNat W :=
      ⟨hpointNonneg, hnatlo, hnathi, hcopPoint⟩
    unfold harmonicLaw
    rw [if_pos hvalid, ← hrootCast x hx]
  have hpointZero (x : ℕ) (hx : x < q) (hc : ¬ Nat.Coprime base W) :
      mu A N i (p_g3_cellPoint A N l C x) = 0 := by
    have hbnds := p_g3_cellPoint_bounds A N i l hq C hC x (by simpa [q] using hx)
    have hpointNonneg : 0 ≤ p_g3_cellPoint A N l C x :=
      le_trans (by exact_mod_cast (A.Xpos N i).le) hbnds.1
    have hnatlo : X ≤ (p_g3_cellPoint A N l C x).toNat := by
      have hnatloInt : (X : ℤ) ≤ ((p_g3_cellPoint A N l C x).toNat : ℤ) := by
        simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.1
      exact_mod_cast hnatloInt
    have hnathi : (p_g3_cellPoint A N l C x).toNat < X ^ 2 := by
      have hnathiInt : ((p_g3_cellPoint A N l C x).toNat : ℤ) < (X : ℤ) ^ 2 := by
        simpa [Int.toNat_of_nonneg hpointNonneg] using hbnds.2
      exact_mod_cast hnathiInt
    have hcopPoint : ¬ Nat.Coprime (p_g3_cellPoint A N l C x).toNat W := by
      intro hc'
      have hc'' : Nat.Coprime (base + M * x) W := by
        rw [← hrootCast x hx] at hc'
        exact hc'
      exact hc ((hcop x).1 hc'')
    change harmonicLaw X W (p_g3_cellPoint A N l C x) = 0
    have hfalse : ¬ (0 ≤ p_g3_cellPoint A N l C x ∧
        X ≤ (p_g3_cellPoint A N l C x).toNat ∧
        (p_g3_cellPoint A N l C x).toNat < X ^ 2 ∧
        Nat.Coprime (p_g3_cellPoint A N l C x).toNat W) := by
      rintro ⟨_, _, _, hc'⟩
      exact hcopPoint hc'
    unfold harmonicLaw
    rw [if_neg hfalse]
  by_cases hc : Nat.Coprime base W
  · let y : Fin q → ℝ := fun x => (base + M * x.val : ℕ)
    let f : Fin q → ℝ := fun x => g x.val
    letI : NeZero q := ⟨by omega⟩
    letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    have hbaseNat : 0 < base := by exact_mod_cast hbasePos
    have hvalPos (x : Fin q) : 0 < ((base + M * x.val : ℕ) : ℝ) := by
      have hnat : 0 < base + M * x.val := by omega
      exact_mod_cast hnat
    have hfactor (x : Fin q) :
        (1 / (y x * harmonicNormalizer X W)) * g x.val =
          ((y x)⁻¹ * g x.val / harmonicNormalizer X W) := by
      field_simp [ne_of_gt (hvalPos x), ne_of_gt hnormPos]
    have hfactorMass (x : Fin q) :
        1 / (y x * harmonicNormalizer X W) =
          (y x)⁻¹ / harmonicNormalizer X W := by
      field_simp [ne_of_gt (hvalPos x), ne_of_gt hnormPos]
    have hy (x : Fin q) : (base : ℝ) ≤ y x ∧ y x ≤ (base : ℝ) + H := by
      constructor
      · dsimp [y]
        exact_mod_cast (Nat.le_add_right base (M * x.val))
      · dsimp [y]
        have hmul : M * x.val < H := by
          calc
            M * x.val < M * q := Nat.mul_lt_mul_of_pos_left x.isLt (A.Mpos N)
            _ = H := hqM
        exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt hmul) base
    have hf (x : Fin q) : |f x| ≤ 1 := hg x.val x.isLt
    have hrecip := p_g3_reciprocalWeights_uniform_expect_diff
      (base : ℝ) (H : ℝ) hbasePos (by positivity) y f hy hf
    let S0 : ℝ := ∑ x : Fin q, (y x)⁻¹
    let T0 : ℝ := ∑ x : Fin q, (y x)⁻¹ * f x
    let U0 : ℝ := (q : ℝ)⁻¹ * ∑ x : Fin q, f x
    have hSpos : 0 < ∑ x : Fin q, (y x)⁻¹ := by
      apply Finset.sum_pos
      · intro x hx
        exact inv_pos.mpr (lt_of_lt_of_le hbasePos (hy x).1)
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩
    have hS0pos : 0 < S0 := by simpa [S0] using hSpos
    have hmuSum :
        (∑ x ∈ Finset.range q, mu A N i (p_g3_cellPoint A N l C x) * g x) =
          T0 / harmonicNormalizer X W := by
      change (∑ x ∈ Finset.range q, mu A N i (p_g3_cellPoint A N l C x) * g x) =
        (∑ x : Fin q, (y x)⁻¹ * f x) / harmonicNormalizer X W
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [y, f]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpointFormula x.val x.isLt hc]
      exact hfactor x
    have hmassSum : p_g3_cellMass A N i l C = S0 / harmonicNormalizer X W := by
      change p_g3_cellMass A N i l C =
        (∑ x : Fin q, (y x)⁻¹) / harmonicNormalizer X W
      rw [p_g3_cellMass, ← Fin.sum_univ_eq_sum_range]
      simp only [y]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpointFormula x.val x.isLt hc]
      exact hfactorMass x
    have havg : (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x = U0 := by
      change (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x =
        (q : ℝ)⁻¹ * ∑ x : Fin q, f x
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hmuSum, hmassSum, havg]
    have hratioBound : |T0 / S0 - U0| ≤ (H : ℝ) / (X : ℝ) := by
      have hcard : Fintype.card (Fin q) = q := Fintype.card_fin _
      have hXposR : 0 < (X : ℝ) := by exact_mod_cast A.Xpos N i
      have hquot : (H : ℝ) / (base : ℝ) ≤ (H : ℝ) / (X : ℝ) := by
        apply (div_le_div_iff₀ hbasePos hXposR).2
        exact mul_le_mul_of_nonneg_left hbaseLower (by positivity)
      simpa [S0, T0, U0, hcard, Fintype.card_fin] using hrecip.trans hquot
    have hscaled (S T Z U : ℝ) (hS : S ≠ 0) (hZ : Z ≠ 0) :
        T / Z - S / Z * U = S / Z * (T / S - U) := by
      field_simp [hS, hZ]
    have hSratioPos : 0 < S0 / harmonicNormalizer X W := div_pos hS0pos hnormPos
    rw [hscaled S0 T0 (harmonicNormalizer X W) U0 (ne_of_gt hS0pos)
      (ne_of_gt hnormPos),
      abs_mul, abs_of_pos hSratioPos]
    exact mul_le_mul_of_nonneg_left hratioBound (le_of_lt hSratioPos)
  · have hzeroMass : p_g3_cellMass A N i l C = 0 := by
      rw [p_g3_cellMass]
      apply Finset.sum_eq_zero
      intro x hx
      exact hpointZero x (Finset.mem_range.mp hx) hc
    rw [hzeroMass]
    have hzeroNum :
        (∑ x ∈ Finset.range q, mu A N i (p_g3_cellPoint A N l C x) * g x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hpointZero x (Finset.mem_range.mp hx) hc]
      simp
    rw [hzeroNum]
    simp

theorem p_g3_localCellMoment_bounds {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (t : ℕ) (ht : 1 ≤ t) (hq : 0 < p_g3_cellOrder A N l)
    [NeZero (p_g3_cellOrder A N l)]
    (C : ℤ × ℕ) (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1) :
    0 ≤ p_g3_localCellMoment A N i l t C h ∧
      p_g3_localCellMoment A N i l t C h ≤ 1 := by
  let q := p_g3_cellOrder A N l
  letI : NeZero q := ⟨by simpa [q] using hq.ne'⟩
  have hlen : List.replicate t (⊤ : AddSubgroup (ZMod q)) ≠ [] := by
    simp [Nat.ne_of_gt ht]
  have hfBound : ∀ x : ZMod q,
      ‖((h (p_g3_cellPoint A N l C x.val) : ℝ) : ℂ)‖ ≤ 1 := by
    intro x
    simpa using hh (p_g3_cellPoint A N l C x.val)
  constructor
  · simpa [p_g3_localCellMoment, q] using
      (SubgroupBox.boxMoment_re_nonneg hlen
        (fun x => ((h (p_g3_cellPoint A N l C x.val) : ℝ) : ℂ)))
  · simpa [p_g3_localCellMoment, q] using
      (SubgroupBox.boxMoment_re_le_one
        (List.replicate t (⊤ : AddSubgroup (ZMod q)))
        (fun x => ((h (p_g3_cellPoint A N l C x.val) : ℝ) : ℂ)) hfBound)

theorem p_g3_cellWeight_total {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hD : 0 < p_g3_totalCellMass A N i l) :
    ∑ C ∈ p_g3_cells A N i l, p_g3_cellWeight A N i l C = 1 := by
  change (∑ C ∈ p_g3_cells A N i l,
    p_g3_cellMass A N i l C /
      (∑ C' ∈ p_g3_cells A N i l, p_g3_cellMass A N i l C')) = 1
  rw [← Finset.sum_div]
  have hden :
      (∑ C ∈ p_g3_cells A N i l, p_g3_cellMass A N i l C) =
        p_g3_totalCellMass A N i l := rfl
  rw [hden]
  exact div_self (ne_of_gt hD)

theorem p_g3_goodCellWeight_lower {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (t : ℕ) (ht : 1 ≤ t) (hq : 0 < p_g3_cellOrder A N l)
    [NeZero (p_g3_cellOrder A N l)]
    (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1) (lam : ℝ)
    (hlam : 0 < lam)
    (hD : 0 < p_g3_totalCellMass A N i l)
    (hglobal : lam ≤ p_g3_cellGlobalMoment A N i l t h) :
    lam / 2 ≤ ∑ C ∈ p_g3_goodCells A N i l t h lam, p_g3_cellWeight A N i l C := by
  classical
  let Cells := p_g3_cells A N i l
  let Good := p_g3_goodCells A N i l t h lam
  let w : (ℤ × ℕ) → ℝ := p_g3_cellWeight A N i l
  let m : (ℤ × ℕ) → ℝ := fun C => p_g3_localCellMoment A N i l t C h
  have htotal := p_g3_cellWeight_total A N i l hD
  have hw (C : ℤ × ℕ) (hC : C ∈ Cells) : 0 ≤ w C := by
    dsimp [w, p_g3_cellWeight]
    have hnum : 0 ≤ p_g3_cellMass A N i l C := by
      unfold p_g3_cellMass
      apply Finset.sum_nonneg
      intro x hx
      exact mu_nonneg A N i (p_g3_cellPoint A N l C x)
    exact div_nonneg hnum hD.le
  have hm (C : ℤ × ℕ) (hC : C ∈ Cells) : 0 ≤ m C ∧ m C ≤ 1 := by
    exact p_g3_localCellMoment_bounds A N i l t ht hq C h hh
  have hpt (C : ℤ × ℕ) (hC : C ∈ Cells) :
      w C * m C ≤ w C * (lam / 2 + if C ∈ Good then 1 else 0) := by
    have hwC := hw C hC
    have hmC := hm C hC
    by_cases hgood : C ∈ Good
    · have hupper : m C ≤ lam / 2 + 1 := by linarith [hmC.2, hlam.le]
      simpa [hgood] using mul_le_mul_of_nonneg_left hupper hwC
    · have hlow : m C < lam / 2 := by
        have hnotgood : ¬ lam / 2 ≤ m C := by
          intro hthreshold
          apply hgood
          exact Finset.mem_filter.mpr ⟨hC, by simpa [m] using hthreshold⟩
        exact lt_of_not_ge hnotgood
      have hupper : m C ≤ lam / 2 := le_of_lt hlow
      simpa [hgood] using mul_le_mul_of_nonneg_left hupper hwC
  have hglobalEq :
      p_g3_cellGlobalMoment A N i l t h = ∑ C ∈ Cells, w C * m C := by
    have hqne : p_g3_cellOrder A N l ≠ 0 := by omega
    simp [p_g3_cellGlobalMoment, hqne, Cells, w, m, p_g3_localCellMoment]
  have hsumBound :
      (∑ C ∈ Cells, w C * m C) ≤
        ∑ C ∈ Cells, w C * (lam / 2 + if C ∈ Good then 1 else 0) := by
    apply Finset.sum_le_sum
    intro C hC
    exact hpt C hC
  have hsumRewrite :
      ∑ C ∈ Cells, w C * (lam / 2 + if C ∈ Good then 1 else 0) =
        lam / 2 * (∑ C ∈ Cells, w C) +
          ∑ C ∈ Good, w C := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hfilter :
        (∑ C ∈ Cells, w C * if C ∈ Good then 1 else 0) =
          ∑ C ∈ Good, w C := by
      calc
        _ = ∑ C ∈ Cells, if lam / 2 ≤ m C then w C else 0 := by
          apply Finset.sum_congr rfl
          intro C hC
          by_cases hg : lam / 2 ≤ m C <;>
            simp [Good, p_g3_goodCells, Cells, m, hC, hg]
        _ = ∑ C ∈ Good, w C := by
          unfold Good
          rw [← Finset.sum_filter]
          simp [p_g3_goodCells, Cells, m]
    rw [hfilter]
    ring
  have hle : lam ≤ lam / 2 * (∑ C ∈ Cells, w C) + ∑ C ∈ Good, w C := by
    rw [hglobalEq] at hglobal
    exact hglobal.trans (hsumBound.trans_eq hsumRewrite)
  rw [htotal] at hle
  have hresult : lam / 2 ≤ ∑ C ∈ Good, w C := by linarith
  simpa [Good, w] using hresult

private theorem p_g3_expect_top_addSubgroup {G : Type*} [AddCommGroup G] [Fintype G]
    (f : (⊤ : AddSubgroup G) → ℂ) (g : G → ℂ)
    (h : ∀ x, f x = g (x : G)) : (𝔼 x : (⊤ : AddSubgroup G), f x) = 𝔼 x : G, g x := by
  exact Fintype.expect_equiv AddSubgroup.topEquiv.toEquiv f g (fun x => by simpa using h x)

/-- The subgroup box moment in full cyclic directions is OpenAI's Gowers moment. -/
theorem p_g3_boxMoment_replicate_top (t : ℕ) {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) :
    SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup G)) f =
      OAI.Erdos3.gowersMoment t f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
      rw [List.replicate_succ]
      simp only [SubgroupBox.boxMoment, OAI.Erdos3.gowersMoment]
      calc
        _ = 𝔼 h : (⊤ : AddSubgroup G),
            OAI.Erdos3.gowersMoment t (OAI.Erdos3.multiplicativeDerivative f h) := by
              change (𝔼 h ∈ (Finset.univ : Finset (⊤ : AddSubgroup G)),
                SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup G))
                  (SubgroupBox.mderiv f h)) =
                𝔼 h ∈ (Finset.univ : Finset (⊤ : AddSubgroup G)),
                  OAI.Erdos3.gowersMoment t
                    (OAI.Erdos3.multiplicativeDerivative f h)
              apply Finset.expect_congr rfl
              intro h hh
              rw [ih]
              rfl
        _ = 𝔼 h : G, OAI.Erdos3.gowersMoment t
            (OAI.Erdos3.multiplicativeDerivative f h) := by
              apply p_g3_expect_top_addSubgroup
              intro h
              rfl
        _ = OAI.Erdos3.gowersMoment (t + 1) f := rfl

/-- A box moment lower bound gives the corresponding cyclic Gowers norm lower bound. -/
theorem p_g3_gowersNorm_lower_of_boxMoment {t q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (a : ℝ) (ha : 0 < a) (ht : 1 ≤ t)
    (hm : a ^ (2 ^ t) ≤
      (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
        (fun x => (f x : ℂ))).re) :
    a ≤ OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) := by
  have hp := OAI.Erdos3.gowersNorm_pow (t - 1) (fun x : ZMod q => (f x : ℂ))
  have hp' :
      OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) ^ (2 ^ t) =
        (OAI.Erdos3.gowersMoment t (fun x => (f x : ℂ))).re := by
    simpa [Nat.sub_add_cancel ht] using hp
  have hbox := p_g3_boxMoment_replicate_top t (fun x : ZMod q => (f x : ℂ))
  have hpow : a ^ (2 ^ t) ≤
      OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) ^ (2 ^ t) := by
    calc
      _ ≤ (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
          (fun x => (f x : ℂ))).re := hm
      _ = (OAI.Erdos3.gowersMoment t (fun x => (f x : ℂ))).re := by rw [hbox]
      _ = _ := hp'.symm
  have hn : 0 ≤ OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) := by
    simpa [Nat.sub_add_cancel ht] using
      OAI.Erdos3.gowersNorm_nonneg (t - 1) (fun x => (f x : ℂ))
  exact (pow_le_pow_iff_left₀ ha.le hn (by positivity : 2 ^ t ≠ 0)).mp hpow

private theorem p_g3_pow_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) : x ^ n ≤ x := by
  have haux : ∀ m : ℕ, x ^ (m + 1) ≤ x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        calc
          x ^ (m + 1) * x ≤ x * x := mul_le_mul_of_nonneg_right ih hx0
          _ ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  simpa [Nat.sub_add_cancel hn] using haux (n - 1)

/-- A normalized local moment above `a` gives Gowers norm at least `a` when `0<a≤1`. -/
theorem p_g3_gowersNorm_lower_of_moment {t q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t)
    (hm : a ≤
      (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
        (fun x => (f x : ℂ))).re) :
    a ≤ OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) := by
  have hpow := OAI.Erdos3.gowersNorm_pow (t - 1) (fun x : ZMod q => (f x : ℂ))
  have hpow' :
      OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) ^ (2 ^ t) =
        (OAI.Erdos3.gowersMoment t (fun x => (f x : ℂ))).re := by
    simpa [Nat.sub_add_cancel ht] using hpow
  have hbox := p_g3_boxMoment_replicate_top t (fun x : ZMod q => (f x : ℂ))
  have hmoment : a ≤
      OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) ^ (2 ^ t) := by
    calc
      a ≤ (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
          (fun x => (f x : ℂ))).re := hm
      _ = (OAI.Erdos3.gowersMoment t (fun x => (f x : ℂ))).re := by rw [hbox]
      _ = _ := hpow'.symm
  have hn : 1 ≤ 2 ^ t := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hnorm0 : 0 ≤ OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) := by
    simpa [Nat.sub_add_cancel ht] using
      OAI.Erdos3.gowersNorm_nonneg (t - 1) (fun x => (f x : ℂ))
  by_contra hnot
  have hlt : OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) < a := lt_of_not_ge hnot
  have hle1 : OAI.Erdos3.gowersNorm t (fun x => (f x : ℂ)) ≤ 1 := hlt.le.trans ha1
  have hpowle := p_g3_pow_le_self hnorm0 hle1 (2 ^ t) hn
  linarith

theorem p_g3_cellInverse_exists {K t : ℕ} {A : Parameters K} {i l : Fin K}
    {M0 : Menu (2 * (t - 1))} {L : ℝ≥0} {cInv a : ℝ}
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t)
    (N : ℕ) (hq : 0 < p_g3_cellOrder A N l)
    [NeZero (p_g3_cellOrder A N l)] (C : ℤ × ℕ)
    (hC : C ∈ p_g3_cells A N i l) (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
    (hgood : a ≤ p_g3_localCellMoment A N i l t C h) :
    ∃ P : CosetPiece M0 L,
      cInv ≤ 𝔼 x : ZMod (p_g3_cellOrder A N l),
        h (p_g3_cellPoint A N l C x.val) *
          (2 * P.eval ((x.val : ℕ) : ℤ) - 1) := by
  let q := p_g3_cellOrder A N l
  letI : NeZero (p_g3_cellOrder A N l) := ⟨hq.ne'⟩
  letI : NeZero q := ⟨by simpa [q] using hq.ne'⟩
  let v : ZMod q → ℝ := fun x => h (p_g3_cellPoint A N l C x.val)
  have hv : ∀ x, |v x| ≤ 1 := fun x => hh _
  have hm : a ≤
      (SubgroupBox.boxMoment (List.replicate t (⊤ : AddSubgroup (ZMod q)))
        (fun x => (v x : ℂ))).re := by
    simpa [p_g3_localCellMoment, q, v] using hgood
  have hnorm : a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) :=
    p_g3_gowersNorm_lower_of_moment v a ha ha1 ht hm
  obtain ⟨P, hcorr⟩ := hInv q v hv hnorm
  refine ⟨P, ?_⟩
  simpa [v, q] using hcorr

noncomputable def p_g3_cellInversePiece {K t : ℕ} {A : Parameters K} {i l : Fin K}
    {M0 : Menu (2 * (t - 1))} {L : ℝ≥0} {cInv a : ℝ}
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t)
    (N : ℕ) (hq : 0 < p_g3_cellOrder A N l)
    [NeZero (p_g3_cellOrder A N l)]
    (C : ℤ × ℕ) (hC : C ∈ p_g3_cells A N i l)
    (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
    (hgood : a ≤ p_g3_localCellMoment A N i l t C h) : CosetPiece M0 L :=
  Classical.choose (p_g3_cellInverse_exists hInv ha ha1 ht N hq C hC h hh hgood)

theorem p_g3_cellInversePiece_spec {K t : ℕ} {A : Parameters K} {i l : Fin K}
    {M0 : Menu (2 * (t - 1))} {L : ℝ≥0} {cInv a : ℝ}
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t)
    (N : ℕ) (hq : 0 < p_g3_cellOrder A N l)
    [NeZero (p_g3_cellOrder A N l)]
    (C : ℤ × ℕ) (hC : C ∈ p_g3_cells A N i l)
    (h : ℤ → ℝ) (hh : ∀ y, |h y| ≤ 1)
    (hgood : a ≤ p_g3_localCellMoment A N i l t C h) :
    cInv ≤ 𝔼 x : ZMod (p_g3_cellOrder A N l),
      h (p_g3_cellPoint A N l C x.val) *
        (2 * (p_g3_cellInversePiece hInv ha ha1 ht N hq C hC h hh hgood).eval
          ((x.val : ℕ) : ℤ) - 1) := by
  have hspec := Classical.choose_spec
    (p_g3_cellInverse_exists hInv ha ha1 ht N hq C hC h hh hgood)
  simpa [p_g3_cellInversePiece] using hspec

noncomputable def p_g3_cellPiece {K t : ℕ} (A : Parameters K) (i l : Fin K)
    (M0 : Menu (2 * (t - 1))) (L : ℝ≥0) (cInv a : ℝ)
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t)
    (Pdefault : CosetPiece M0 L) (h : ℕ → ℤ → ℝ)
    (hh : ∀ N y, |h N y| ≤ 1) (N : ℕ) (C : ℤ × ℕ) : CosetPiece M0 L := by
  classical
  by_cases hq0 : p_g3_cellOrder A N l = 0
  · exact Pdefault
  · haveI : NeZero (p_g3_cellOrder A N l) := ⟨hq0⟩
    by_cases hC : C ∈ p_g3_cells A N i l
    · by_cases hgood : a ≤ p_g3_localCellMoment A N i l t C (h N)
      · have hq : 0 < p_g3_cellOrder A N l := Nat.pos_of_ne_zero hq0
        exact (p_g3_cellInversePiece hInv ha ha1 ht N hq C hC
          (h N) (hh N) hgood).shift
            (-(C.1 * (p_g3_cellOrder A N l : ℤ)))
      · exact Pdefault
    · exact Pdefault

theorem p_g3_cellPiece_good {K t : ℕ} (A : Parameters K) (i l : Fin K)
    (M0 : Menu (2 * (t - 1))) (L : ℝ≥0) (cInv a : ℝ)
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (Pdefault : CosetPiece M0 L)
    (h : ℕ → ℤ → ℝ) (hh : ∀ N y, |h N y| ≤ 1) (N : ℕ) (C : ℤ × ℕ)
    (hq : 0 < p_g3_cellOrder A N l) [NeZero (p_g3_cellOrder A N l)]
    (hC : C ∈ p_g3_cells A N i l)
    (hgood : a ≤ p_g3_localCellMoment A N i l t C (h N)) :
    p_g3_cellPiece A i l M0 L cInv a hInv ha ha1 ht Pdefault h hh N C =
      (p_g3_cellInversePiece hInv ha ha1 ht N hq C hC (h N) (hh N) hgood).shift
        (-(C.1 * (p_g3_cellOrder A N l : ℤ))) := by
  classical
  simp [p_g3_cellPiece, ne_of_gt hq, hC, hgood]

theorem p_g3_cellPiece_default_of_not_good {K t : ℕ} (A : Parameters K) (i l : Fin K)
    (M0 : Menu (2 * (t - 1))) (L : ℝ≥0) (cInv a lam : ℝ)
    (hInv : ∀ (q : ℕ) [NeZero q] (v : ZMod q → ℝ), (∀ x, |v x| ≤ 1) →
      a ≤ OAI.Erdos3.gowersNorm t (fun x => (v x : ℂ)) →
        ∃ P : CosetPiece M0 L,
          cInv ≤ 𝔼 x : ZMod q, v x * (2 * P.eval ((x.val : ℕ) : ℤ) - 1))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (Pdefault : CosetPiece M0 L)
    (h : ℕ → ℤ → ℝ) (hh : ∀ N y, |h N y| ≤ 1) (N : ℕ) (C : ℤ × ℕ)
    (hq : 0 < p_g3_cellOrder A N l) [NeZero (p_g3_cellOrder A N l)]
    (hnot : C ∉ p_g3_goodCells A N i l t (h N) lam) (haEq : a = lam / 2) :
    p_g3_cellPiece A i l M0 L cInv a hInv ha ha1 ht Pdefault h hh N C = Pdefault := by
  classical
  by_cases hC : C ∈ p_g3_cells A N i l
  · have hgood : ¬ a ≤ p_g3_localCellMoment A N i l t C (h N) := by
      intro hm
      apply hnot
      exact Finset.mem_filter.mpr ⟨hC, by rw [← haEq]; exact hm⟩
    simp [p_g3_cellPiece, ne_of_gt hq, hC, hgood]
  · simp [p_g3_cellPiece, ne_of_gt hq, hC]

theorem p_g3_cellPoint_progressionCoordinates {K : ℕ} (A : Parameters K) (N : ℕ)
    (i l : Fin K) (hq : 0 < p_g3_cellOrder A N l) (C : ℤ × ℕ)
    (hC : C ∈ p_g3_cells A N i l) (x : ℕ)
    (hx : x < p_g3_cellOrder A N l) :
    (p_g3_cellPoint A N l C x) / (A.H N l : ℤ) = C.1 ∧
      (p_g3_cellPoint A N l C x) % (A.M N : ℤ) = C.2 ∧
      (p_g3_cellPoint A N l C x - (C.2 : ℤ)) / (A.M N : ℤ) =
        C.1 * (p_g3_cellOrder A N l : ℤ) + x := by
  classical
  let q := p_g3_cellOrder A N l
  let M := A.M N
  let H := A.H N l
  have hdiv := p_g3_point_div_mod A N i l hq C hC x hx
  have hqM : M * q = H := by
    dsimp [M, H, q, p_g3_cellOrder]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel (A.Hdiv N l)
  have hHcast : (H : ℤ) = (M : ℤ) * (q : ℤ) := by exact_mod_cast hqM.symm
  have hPointEq : p_g3_cellPoint A N l C x =
      (C.2 : ℤ) + (M : ℤ) * (C.1 * (q : ℤ) + x) := by
    simp [p_g3_cellPoint, M, H, hHcast] <;> ring
  have hCmemParts : C.1 ∈ p_g3_fullIntervals A N i l ∧ C.2 < M := by
    simpa [p_g3_cells, M] using hC
  have hCmem : C.2 < M := hCmemParts.2
  have hMpos : 0 < (M : ℤ) := by exact_mod_cast A.Mpos N
  have hMne : (M : ℤ) ≠ 0 := hMpos.ne'
  have hρ0 : (0 : ℤ) ≤ (C.2 : ℤ) := by positivity
  have hρlt : (C.2 : ℤ) < (M : ℤ) := by exact_mod_cast hCmem
  have hmodM : p_g3_cellPoint A N l C x % (M : ℤ) = C.2 := by
    rw [hPointEq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hρ0 hρlt]
  refine ⟨hdiv.1, hmodM, ?_⟩
  calc
    (p_g3_cellPoint A N l C x - (C.2 : ℤ)) / (M : ℤ) =
        (M : ℤ) * (C.1 * (q : ℤ) + x) / (M : ℤ) := by rw [hPointEq]; ring
    _ = C.1 * (q : ℤ) + x := Int.mul_ediv_cancel_left _ hMne

theorem p_g3_repFamily_eval_shifted {K s : ℕ} (A : Parameters K) (i l : Fin K)
    (M : Menu s) (L : ℝ≥0) (Φ : RepFamily A l M L) (N : ℕ)
    (C : ℤ × ℕ) (hq : 0 < p_g3_cellOrder A N l)
    (hC : C ∈ p_g3_cells A N i l) (x : ℕ)
    (hx : x < p_g3_cellOrder A N l) (P : CosetPiece M L)
    (hpiece : Φ.piece N C.1 (C.2 : ℤ) =
      P.shift (-(C.1 * (p_g3_cellOrder A N l : ℤ)))) :
    Φ.eval N (p_g3_cellPoint A N l C x) = P.eval x := by
  have hcoords := p_g3_cellPoint_progressionCoordinates A N i l hq C hC x hx
  unfold RepFamily.eval
  rw [hcoords.1, hcoords.2.1, hpiece]
  rw [OAI.SourceMenuLiteral.CosetPiece.shift_eval, hcoords.2.2]
  ring

theorem p_g3_zmod_expect_range {q : ℕ} [NeZero q] (g : ℕ → ℝ) :
    (𝔼 z : ZMod q, g z.val) =
      (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x := by
  classical
  have hval : ∀ x : Fin q, ((ZMod.finEquiv q).toEquiv x).val = x.val := by
    intro x
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => rfl
  have hEquiv :
      (𝔼 x : Fin q, g x.val) = (𝔼 z : ZMod q, g z.val) := by
    exact Fintype.expect_equiv (ZMod.finEquiv q).toEquiv
      (fun x : Fin q => g x.val) (fun z : ZMod q => g z.val) (by
        intro x
        rw [hval x])
  have hFin :
      (𝔼 x : Fin q, g x.val) =
        (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x := by
    rw [Finset.expect_eq_sum_div_card]
    have hcard : (Finset.univ : Finset (Fin q)).card = q := by simp
    rw [hcard]
    have hsum : (∑ x : Fin q, g x.val) = ∑ x ∈ Finset.range q, g x := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [← hsum]
    simp [div_eq_mul_inv, mul_comm]
  exact hEquiv.symm.trans hFin

theorem p_g3_cellOrder_pos {K : ℕ} (A : Parameters K) (N : ℕ) (l : Fin K) :
    0 < p_g3_cellOrder A N l := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (A.Hpos N l) (A.Hdiv N l)
  · exact A.Mpos N

private theorem p_g3_Emu_sq_le_one {K : ℕ} (A : Parameters K) (N : ℕ)
    (i : Fin K) (v : ℤ → ℝ) (hv : ∀ y, |v y| ≤ 1) :
    Emu A N i (fun y => v y * v y) ≤ 1 := by
  rw [Emu_eq_sum_support]
  have hle :
      (∑ y ∈ muSupport A N i, mu A N i y * (v y * v y)) ≤
        ∑ y ∈ muSupport A N i, mu A N i y * 1 := by
    apply Finset.sum_le_sum
    intro y hy
    have hsq : v y * v y ≤ 1 := by nlinarith [abs_le.mp (hv y)]
    exact mul_le_mul_of_nonneg_left hsq (mu_nonneg A N i y)
  calc
    _ ≤ ∑ y ∈ muSupport A N i, mu A N i y * 1 := hle
    _ = Emu A N i (fun _ => 1) := by rw [Emu_eq_sum_support]
    _ ≤ 1 := Emu_mass_le_one A N i

theorem p_g3_familyInner_self_le_one {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (V : ℕ → ℤ → ℝ) (hV : ∀ N y, |V N y| ≤ 1) :
    familyInner A U i V V ≤ 1 := by
  let e : ℕ → ℝ := fun N => Emu A N i (fun y => V N y * V N y)
  have hnonneg : ∀ N, 0 ≤ e N := by
    intro N
    exact Emu_nonneg A N i (fun y => V N y * V N y) (fun y => mul_self_nonneg _)
  have hle : ∀ N, e N ≤ 1 := by
    intro N
    exact p_g3_Emu_sq_le_one A N i (V N) (hV N)
  have hbound : ∃ B : ℝ, ∀ N, |e N| ≤ B := by
    refine ⟨1, ?_⟩
    intro N
    exact abs_le.mpr ⟨by linarith [hnonneg N], hle N⟩
  have htend := ulim_tendsto_of_bounded U e hbound
  change ulim U e ≤ 1
  exact le_of_tendsto_of_tendsto' htend tendsto_const_nhds hle

/-- The affine inverse correlator is in the real span of the representing families. -/
theorem p_g3_affine_repSpan {K : ℕ} {A : Parameters K} {l : Fin K} {s : ℕ}
    {M : Menu s} {L : ℝ≥0} (hM : 0 < M.size) (Φ : RepFamily A l M L) :
    (fun N y => 2 * Φ.eval N y - 1) ∈ repSpan A l s := by
  classical
  obtain ⟨P₁, hP₁⟩ := HindmanSumsProducts.InverseBridge.exists_constPiece hM 1
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  let Ψ : RepFamily A l M L := ⟨fun _ _ _ => P₁⟩
  have hΦ : Φ.eval ∈ repSpan A l s := by
    apply Submodule.subset_span
    exact ⟨M, L, Φ, rfl⟩
  have hΨ : Ψ.eval ∈ repSpan A l s := by
    apply Submodule.subset_span
    exact ⟨M, L, Ψ, rfl⟩
  have hΨeval (N : ℕ) (y : ℤ) : Ψ.eval N y = 1 := by
    simpa [Ψ, RepFamily.eval] using
      hP₁ ((y - y % (A.M N : ℤ)) / (A.M N : ℤ))
  have hEq : (fun N y => 2 * Φ.eval N y - 1) =
      (2 : ℝ) • Φ.eval + (-1 : ℝ) • Ψ.eval := by
    funext N y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hΨeval]
    ring
  rw [hEq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ (2 : ℝ) hΦ)
    (Submodule.smul_mem _ (-1 : ℝ) hΨ)

/-- A bounded correlator witness gives a lower bound for the projection norm. -/
theorem p_g3_projection_from_witness {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i l : Fin K) (s : ℕ) (h V : ℕ → ℤ → ℝ) (c : ℝ)
    (hh : ∃ B, ∀ N y, |h N y| ≤ B) (hVspan : V ∈ repSpan A l s)
    (hVnorm : familyInner A U i V V ≤ 1)
    (hpair : c ≤ familyInner A U i h V) :
  c ≤ projNorm A U i l s h :=
  hpair.trans (le_projNorm A U i l s h V hh hVspan hVnorm)

set_option maxHeartbeats 0 in
theorem p_g3_projection_lower_bound (t : ℕ) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 2 * (t - 1) ≤ s →
      ∀ {K : ℕ} (A : Parameters K) (i l : Fin K), l < i →
      ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
      ∀ h : ℕ → ℤ → ℝ, (∀ N y, |h N y| ≤ 1) →
        (∀ᶠ N in (U : Filter ℕ), δ ^ (2 ^ t) ≤ p_g3_cellGlobalMoment A N i l t (h N)) →
        c ≤ projNorm A U i l s h := by
  classical
  let δ0 : ℝ := min δ 1
  have hδ0 : 0 < δ0 := lt_min hδ (by norm_num)
  have hδ0le1 : δ0 ≤ 1 := min_le_right δ 1
  have hδ0leδ : δ0 ≤ δ := min_le_left δ 1
  let lam : ℝ := δ0 ^ (2 ^ t)
  have hlam : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    exact pow_le_one₀ hδ0.le hδ0le1
  have hpowδ : lam ≤ δ ^ (2 ^ t) := by
    dsimp [lam]
    exact pow_le_pow_left₀ hδ0.le hδ0leδ _
  let a : ℝ := lam / 2
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have ht1 : 1 ≤ t := by omega
  obtain ⟨M0, L, cInv, hM0, hcInv, hInv⟩ :=
    HindmanSumsProducts.InverseBridge.cyclic_inverse_menu t ht a ha
  let c : ℝ := lam * cInv / 8
  have hc : 0 < c := by positivity
  refine ⟨c, hc, ?_⟩
  intro s hs K A i l hli U hU h hh hMoment
  let Hsq : ℕ → ℝ := fun N => (A.H N l : ℝ) ^ 2 / (A.X N i : ℝ)
  let HoverX : ℕ → ℝ := fun N => (A.H N l : ℝ) / (A.X N i : ℝ)
  let cellError : ℕ → ℝ := fun N =>
    8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) / (A.X N i : ℝ)
  have hHsq := p_g3_Hsq_over_X_tendsto A i l hli
  have hErr := p_g3_cellError_tendsto A i l hli
  have hHsqSmall1 : ∀ᶠ N in atTop, Hsq N < 1 := by
    exact hHsq.eventually (Iio_mem_nhds (by norm_num))
  have hHsqSmallC : ∀ᶠ N in atTop, Hsq N < cInv / 2 := by
    exact hHsq.eventually (Iio_mem_nhds (by positivity))
  have hErrorSmall : ∀ᶠ N in atTop, cellError N < 1 / 2 := by
    exact hErr.eventually (Iio_mem_nhds (by norm_num))
  have hHleX : ∀ᶠ N in atTop, A.H N l ≤ A.X N i := by
    filter_upwards [hHsqSmall1] with N hsmall
    have hH1 : (1 : ℝ) ≤ (A.H N l : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (A.Hpos N l).ne'
    have hHleSq : (A.H N l : ℝ) ≤ (A.H N l : ℝ) ^ 2 := by nlinarith
    have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
    have hsq : (A.H N l : ℝ) ^ 2 < (A.X N i : ℝ) := by
      have hsq' := (div_lt_iff₀ hXpos).mp (by simpa [Hsq] using hsmall)
      nlinarith [hsq']
    exact_mod_cast (le_of_lt (hHleSq.trans_lt hsq))
  have hHoverXsmall : ∀ᶠ N in atTop, HoverX N < cInv / 2 := by
    filter_upwards [hHsqSmallC, Filter.Eventually.of_forall (fun N => A.Xpos N i),
      Filter.Eventually.of_forall (fun N => A.Hpos N l)] with N hsmall hX hH
    have hH1 : (1 : ℝ) ≤ (A.H N l : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hH.ne')
    have hHleSq : (A.H N l : ℝ) ≤ (A.H N l : ℝ) ^ 2 := by nlinarith
    have hquot := div_le_div_of_nonneg_right hHleSq (by positivity : 0 ≤ (A.X N i : ℝ))
    have hquot' : HoverX N ≤ Hsq N := by simpa [HoverX, Hsq] using hquot
    exact hquot'.trans_lt hsmall
  have hScaleAtTop : ∀ᶠ N in atTop,
      4 * primorial (N + 1) ≤ A.X N i ∧ A.H N l ≤ A.X N i ∧
        cellError N < 1 / 2 ∧ HoverX N < cInv / 2 := by
    filter_upwards [A.eventual_X i, hHleX, hErrorSmall, hHoverXsmall]
      with N hcut hHX herr hratio
    exact ⟨hcut, hHX, by simpa [cellError] using herr,
      by simpa [HoverX] using hratio⟩
  have hScaleU : ∀ᶠ N in (U : Filter ℕ),
      4 * primorial (N + 1) ≤ A.X N i ∧ A.H N l ≤ A.X N i ∧
        cellError N < 1 / 2 ∧ HoverX N < cInv / 2 := by
    have hScaleCof : ∀ᶠ N in Filter.cofinite,
        4 * primorial (N + 1) ≤ A.X N i ∧ A.H N l ≤ A.X N i ∧
          cellError N < 1 / 2 ∧ HoverX N < cInv / 2 := by
      simpa only [Nat.cofinite_eq_atTop] using hScaleAtTop
    exact Filter.Eventually.filter_mono hU hScaleCof
  have hMomentLam : ∀ᶠ N in (U : Filter ℕ),
      lam ≤ p_g3_cellGlobalMoment A N i l t (h N) := by
    filter_upwards [hMoment] with N hN
    exact hpowδ.trans hN
  let Pdefault : CosetPiece M0 L :=
    Classical.choose (HindmanSumsProducts.InverseBridge.exists_constPiece hM0
      (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  have hPdefault : ∀ k, Pdefault.eval k = 1 / 2 :=
    Classical.choose_spec (HindmanSumsProducts.InverseBridge.exists_constPiece hM0
      (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  let choosePiece : ℕ → (ℤ × ℕ) → CosetPiece M0 L := fun N C =>
    p_g3_cellPiece A i l M0 L cInv a hInv ha ha1 ht1 Pdefault h hh N C
  let Φ : RepFamily A l M0 L := ⟨fun N k r => choosePiece N (k, r.toNat)⟩
  let V : ℕ → ℤ → ℝ := fun N y => 2 * Φ.eval N y - 1
  have hΦrange : ∀ N y, Φ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
    intro N y
    change (Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))).eval
      ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) ∈ Set.Icc (0 : ℝ) 1
    exact (Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))).range _
  have hVbound : ∀ N y, |V N y| ≤ 1 := by
    intro N y
    have hr := hΦrange N y
    dsimp [V]
    rw [abs_le]
    constructor <;> rcases hr with ⟨h0, h1⟩ <;> nlinarith
  have hVspan : V ∈ repSpan A l s := by
    have hV0 := p_g3_affine_repSpan hM0 Φ
    exact (repSpan_mono_step A l hs) hV0
  have hVnorm : familyInner A U i V V ≤ 1 :=
    p_g3_familyInner_self_le_one A U i V hVbound
  let pair : ℕ → ℝ := fun N => Emu A N i (fun y => h N y * V N y)
  have hpairBound : ∃ B : ℝ, ∀ N, |pair N| ≤ B := by
    refine ⟨1, ?_⟩
    intro N
    have hV2 := p_g3_Emu_sq_le_one A N i (V N) (hVbound N)
    have hmass := Emu_mass_le_one A N i
    have habs := Emu_abs_inner_le A N i (h N) (V N) 1 (by norm_num) (hh N)
    have hlocal : |pair N| ≤
        (Emu A N i (fun _ => 1) + Emu A N i (fun y => V N y * V N y)) / 2 := by
      simpa [pair] using habs
    linarith
  have hpairEvent : ∀ᶠ N in (U : Filter ℕ), c ≤ pair N := by
    filter_upwards [hMomentLam, hScaleU] with N hGlobal hScale
    have hq : 0 < p_g3_cellOrder A N l := p_g3_cellOrder_pos A N l
    letI : NeZero (p_g3_cellOrder A N l) := ⟨hq.ne'⟩
    let Good := p_g3_goodCells A N i l t (h N) lam
    have hGoodSubset : Good ⊆ p_g3_cells A N i l := by
      intro C hC
      exact (Finset.mem_filter.mp hC).1
    have hDlower :
        1 - 8 * (A.H N l : ℝ) * (primorial (N + 1) : ℝ) /
          (A.X N i : ℝ) ≤ p_g3_totalCellMass A N i l := by
      simpa [cellError] using
        (p_g3_totalCellMass_lower A N i l hq hScale.1 hScale.2.1)
    have hDhalf : (1 / 2 : ℝ) ≤ p_g3_totalCellMass A N i l := by
      have herr := hScale.2.2.1
      dsimp [cellError] at herr
      linarith
    have hDpos : 0 < p_g3_totalCellMass A N i l :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hDhalf
    have hGoodWeight : lam / 2 ≤
        ∑ C ∈ Good, p_g3_cellWeight A N i l C := by
      exact p_g3_goodCellWeight_lower A N i l t ht1 hq (h N) (hh N) lam hlam
        hDpos hGlobal
    have hGoodMassEq :
        p_g3_totalCellMass A N i l *
            (∑ C ∈ Good, p_g3_cellWeight A N i l C) =
          ∑ C ∈ Good, p_g3_cellMass A N i l C := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C hC
      dsimp [p_g3_cellWeight]
      have hden :
          (∑ C' ∈ p_g3_cells A N i l, p_g3_cellMass A N i l C') =
            p_g3_totalCellMass A N i l := rfl
      rw [hden]
      field_simp [ne_of_gt hDpos]
    have hGoodMass : lam / 4 ≤
        ∑ C ∈ Good, p_g3_cellMass A N i l C := by
      have hprod := mul_le_mul hDhalf hGoodWeight (by positivity) (by linarith [hDhalf])
      calc
        lam / 4 = (1 / 2) * (lam / 2) := by ring
        _ ≤ p_g3_totalCellMass A N i l *
            (∑ C ∈ Good, p_g3_cellWeight A N i l C) := hprod
        _ = _ := hGoodMassEq
    let GoodPairs := Good.product (Finset.range (p_g3_cellOrder A N l))
    let GoodImage := GoodPairs.image
      (fun p : (ℤ × ℕ) × ℕ => p_g3_cellPoint A N l p.1 p.2)
    have hzero (z : ℤ) (hz : z ∈ muSupport A N i)
        (hzout : z ∉ GoodImage) : h N z * V N z = 0 := by
      let C : ℤ × ℕ :=
        (z / (A.H N l : ℤ), (z % (A.M N : ℤ)).toNat)
      have hCbad : C ∉ Good := by
        intro hCG
        have hCcell := (Finset.mem_filter.mp hCG).1
        have hCinterval : C.1 ∈ p_g3_fullIntervals A N i l :=
          (Finset.mem_product.mp hCcell).1
        obtain ⟨C', x, hC', hx, hpt⟩ :=
          p_g3_support_decomposition A N i l hq z hz (by simpa [C] using hCinterval)
        have hcoords := p_g3_cellPoint_progressionCoordinates A N i l hq C' hC' x hx
        have hquot : z / (A.H N l : ℤ) = C'.1 := by
          simpa [hpt] using hcoords.1
        have hmod : z % (A.M N : ℤ) = (C'.2 : ℤ) := by
          simpa [hpt] using hcoords.2.1
        have hres : C'.2 = (z % (A.M N : ℤ)).toNat := by
          have h := congrArg Int.toNat hmod
          simpa [Int.toNat_natCast] using h.symm
        have hCeq : C' = C := by
          apply Prod.ext
          · simpa [C] using hquot.symm
          · simpa [C] using hres
        have hC'good : C' ∈ Good := by simpa [hCeq] using hCG
        have himage : z ∈ GoodImage := by
          apply Finset.mem_image.mpr
          exact ⟨(C', x), Finset.mem_product.mpr
            ⟨hC'good, Finset.mem_range.mpr hx⟩, hpt⟩
        exact hzout himage
      have hpieceDefault : choosePiece N C = Pdefault := by
        have hp := p_g3_cellPiece_default_of_not_good A i l M0 L cInv a lam
          hInv ha ha1 ht1 Pdefault h hh N C hq hCbad rfl
        simpa [choosePiece] using hp
      have hEvalDefault : Φ.eval N z = 1 / 2 := by
        change (choosePiece N C).eval ((z - z % (A.M N : ℤ)) /
          (A.M N : ℤ)) = 1 / 2
        rw [hpieceDefault]
        exact hPdefault _
      simp [V, hEvalDefault]
    have hpairEq : pair N =
        ∑ C ∈ Good, ∑ x ∈ Finset.range (p_g3_cellOrder A N l),
          mu A N i (p_g3_cellPoint A N l C x) *
            (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
      have hEmu := p_g3_Emu_eq_sum_on_finite_set A N i GoodImage
        (fun z => h N z * V N z) hzero
      have himage := p_g3_sum_image_cells A N i l hq Good hGoodSubset
        (fun z => mu A N i z * (h N z * V N z))
      calc
        pair N = Emu A N i (fun z => h N z * V N z) := by rfl
        _ = ∑ z ∈ GoodImage, mu A N i z * (h N z * V N z) := hEmu
        _ = ∑ C ∈ Good, ∑ x ∈ Finset.range (p_g3_cellOrder A N l),
            mu A N i (p_g3_cellPoint A N l C x) *
              (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
                rw [himage]
    have hCellLower : c ≤ pair N := by
      let q := p_g3_cellOrder A N l
      have hCellBound (C : ℤ × ℕ) (hCG : C ∈ Good) :
          (cInv / 2) * p_g3_cellMass A N i l C ≤
            ∑ x ∈ Finset.range q,
              mu A N i (p_g3_cellPoint A N l C x) *
                (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
        have hparts := Finset.mem_filter.mp hCG
        have hC : C ∈ p_g3_cells A N i l := hparts.1
        have hgood : a ≤ p_g3_localCellMoment A N i l t C (h N) := by
          simpa [a, p_g3_goodCells] using hparts.2
        let P := p_g3_cellInversePiece hInv ha ha1 ht1 N hq C hC
          (h N) (hh N) hgood
        have hp := p_g3_cellPiece_good A i l M0 L cInv a hInv ha ha1 ht1
          Pdefault h hh N C hq hC hgood
        have hpiece : Φ.piece N C.1 (C.2 : ℤ) =
            P.shift (-(C.1 * (p_g3_cellOrder A N l : ℤ))) := by
          simpa [Φ, choosePiece, P, Int.toNat_natCast] using hp
        have hVAt (x : ℕ) (hx : x < q) :
            V N (p_g3_cellPoint A N l C x) = 2 * P.eval (x : ℤ) - 1 := by
          have hEval := p_g3_repFamily_eval_shifted A i l M0 L Φ N C hq hC x hx P hpiece
          simp [V, hEval]
        -- The cell inverse correlator has a positive uniform average.
        let g : ℕ → ℝ := fun x => h N (p_g3_cellPoint A N l C x) *
          (2 * P.eval (x : ℤ) - 1)
        have hP01 (x : ℕ) : P.eval (x : ℤ) ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [OAI.SourceMenuLiteral.CosetPiece.eval] using
            P.range (P.g ^ (x : ℤ) • P.x)
        have hg : ∀ x < q, |g x| ≤ 1 := by
          intro x hx
          have hhx := hh N (p_g3_cellPoint A N l C x)
          have haff : |2 * P.eval (x : ℤ) - 1| ≤ 1 := by
            rcases hP01 x with ⟨hlo, hhi⟩
            rw [abs_le]
            constructor <;> nlinarith
          change |h N (p_g3_cellPoint A N l C x) *
            (2 * P.eval (x : ℤ) - 1)| ≤ 1
          rw [abs_mul]
          calc
            |h N (p_g3_cellPoint A N l C x)| * |2 * P.eval (x : ℤ) - 1| ≤
                |h N (p_g3_cellPoint A N l C x)| * 1 :=
                  mul_le_mul_of_nonneg_left haff (abs_nonneg _)
            _ ≤ 1 := by simpa using hhx
        have hcorr := p_g3_cellInversePiece_spec hInv ha ha1 ht1 N hq C hC
          (h N) (hh N) hgood
        have huniform : cInv ≤ (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x := by
          calc
            cInv ≤ 𝔼 z : ZMod q, g z.val := by
              simpa [g] using hcorr
            _ = (q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x :=
              p_g3_zmod_expect_range (q := q) g
        have hcompare := p_g3_cellExpectationCompare A N i l hq hScale.1 C hC g hg
        have hmass0 : 0 ≤ p_g3_cellMass A N i l C := by
          unfold p_g3_cellMass
          apply Finset.sum_nonneg
          intro x hx
          exact mu_nonneg A N i (p_g3_cellPoint A N l C x)
        have hrawlower :
            p_g3_cellMass A N i l C * ((q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x) -
                p_g3_cellMass A N i l C * ((A.H N l : ℝ) / (A.X N i : ℝ)) ≤
              ∑ x ∈ Finset.range q,
                mu A N i (p_g3_cellPoint A N l C x) * g x := by
          have hlow := (abs_le.mp hcompare).1
          linarith
        have hlocal :
            p_g3_cellMass A N i l C *
                (cInv - (A.H N l : ℝ) / (A.X N i : ℝ)) ≤
              ∑ x ∈ Finset.range q,
                mu A N i (p_g3_cellPoint A N l C x) * g x := by
          calc
            _ = p_g3_cellMass A N i l C * cInv -
                p_g3_cellMass A N i l C * ((A.H N l : ℝ) / (A.X N i : ℝ)) := by ring
            _ ≤ p_g3_cellMass A N i l C *
                ((q : ℝ)⁻¹ * ∑ x ∈ Finset.range q, g x) -
                  p_g3_cellMass A N i l C * ((A.H N l : ℝ) / (A.X N i : ℝ)) :=
                    sub_le_sub_right (mul_le_mul_of_nonneg_left huniform hmass0) _
            _ ≤ _ := hrawlower
        have hsumEq :
            (∑ x ∈ Finset.range q,
              mu A N i (p_g3_cellPoint A N l C x) * g x) =
              ∑ x ∈ Finset.range q,
                mu A N i (p_g3_cellPoint A N l C x) *
                  (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          dsimp [g]
          rw [hVAt x (Finset.mem_range.mp hx)]
        have hlocalV :
            p_g3_cellMass A N i l C *
                (cInv - (A.H N l : ℝ) / (A.X N i : ℝ)) ≤
              ∑ x ∈ Finset.range q,
                mu A N i (p_g3_cellPoint A N l C x) *
                  (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
          rw [← hsumEq]
          exact hlocal
        have hfactor : cInv / 2 ≤ cInv - (A.H N l : ℝ) / (A.X N i : ℝ) := by
          linarith [hScale.2.2.2]
        calc
          _ = p_g3_cellMass A N i l C * (cInv / 2) := by ring
          _ ≤ p_g3_cellMass A N i l C *
              (cInv - (A.H N l : ℝ) / (A.X N i : ℝ)) :=
                mul_le_mul_of_nonneg_left hfactor hmass0
          _ ≤ _ := hlocalV
      have hsumGood :
          (cInv / 2) *
              (∑ C ∈ Good, p_g3_cellMass A N i l C) ≤
            ∑ C ∈ Good, ∑ x ∈ Finset.range q,
              mu A N i (p_g3_cellPoint A N l C x) *
                (h N (p_g3_cellPoint A N l C x) * V N (p_g3_cellPoint A N l C x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro C hC
        simpa [mul_comm] using hCellBound C hC
      have htarget : c ≤ (cInv / 2) *
          (∑ C ∈ Good, p_g3_cellMass A N i l C) := by
        calc
          c = (cInv / 2) * (lam / 4) := by dsimp [c]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hGoodMass (by positivity)
      rw [hpairEq]
      exact htarget.trans hsumGood
    exact hCellLower
  have htend := ulim_tendsto_of_bounded U pair hpairBound
  have hpairLim : c ≤ familyInner A U i h V := by
    change c ≤ ulim U pair
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hpairEvent
  exact p_g3_projection_from_witness A U i l s h V c
    ⟨1, fun N y => hh N y⟩ hVspan hVnorm hpairLim

end HindmanSumsProducts.Prediction
