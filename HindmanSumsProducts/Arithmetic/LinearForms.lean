import HindmanSumsProducts.Arithmetic.RoughCoprimality
import HindmanSumsProducts.Arithmetic.Sampling
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A homogeneous linear row whose coefficients are rational polynomials in prime slots. -/
structure RationalLinearRow (d m : ℕ) where
  coefficient : Fin d → MvPolynomial (Fin m) ℚ

/-- Rational coefficient of a row after evaluating its prime parameters. -/
def rationalRowCoefficient {d m : ℕ} (L : RationalLinearRow d m)
    (p : Fin m → ℕ) (j : Fin d) : ℚ :=
  MvPolynomial.eval (fun i => (p i : ℚ)) (L.coefficient j)

/-- Rational value of a homogeneous row on integer base variables and prime parameters. -/
def rationalRowValue {d m : ℕ} (L : RationalLinearRow d m)
    (x : Fin d → ℤ) (p : Fin m → ℕ) : ℚ :=
  ∑ j, rationalRowCoefficient L p j * (x j : ℚ)

/-- Integer represented by a rational row value when its denominator is one. -/
def rationalRowIntegerValue {d m : ℕ} (L : RationalLinearRow d m)
    (x : Fin d → ℤ) (p : Fin m → ℕ) : ℤ :=
  (rationalRowValue L x p).num

/-- Value of a row with rational coefficients that may depend on the scale and prime tuple. -/
def linearRowValue {q d m : ℕ} (rowCoeff : ℕ → (Fin m → ℕ) → Fin q → Fin d → ℚ)
    (N : ℕ) (p : Fin m → ℕ) (u : Fin q) (x : Fin d → ℤ) : ℚ :=
  ∑ j, rowCoeff N p u j * (x j : ℚ)

/-- Reduction of a rational coefficient modulo a prime where its denominator is a unit. -/
noncomputable def rationalResidue (p : ℕ) (hp : p.Prime) (r : ℚ) : ZMod p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (r.num : ZMod p) / (r.den : ZMod p)

/-- A rational coefficient reduced modulo an arbitrary modulus coprime to its denominator. -/
noncomputable def rationalResidueModulus (M : ℕ) (r : ℚ)
    (hden : Nat.Coprime r.den M) : ZMod M := by
  let hd : IsUnit (r.den : ZMod M) := (ZMod.isUnit_iff_coprime r.den M).2 hden
  exact (r.num : ZMod M) * ↑(hd.unit⁻¹)

private theorem rationalResidueModulus_cast {K M : ℕ} (hMK : M ∣ K)
    (r : ℚ) (hdenK : Nat.Coprime r.den K) (hdenM : Nat.Coprime r.den M) :
    ZMod.castHom hMK (ZMod M) (rationalResidueModulus K r hdenK) =
      rationalResidueModulus M r hdenM := by
  classical
  let f : ZMod K →+* ZMod M := ZMod.castHom hMK (ZMod M)
  have hdK : IsUnit (r.den : ZMod K) := (ZMod.isUnit_iff_coprime r.den K).2 hdenK
  have hdM : IsUnit (r.den : ZMod M) := (ZMod.isUnit_iff_coprime r.den M).2 hdenM
  have hmapUnit : Units.map f.toMonoidHom hdK.unit = hdM.unit := by
    apply Units.ext
    change f (↑hdK.unit) = ↑hdM.unit
    rw [hdK.unit_spec, hdM.unit_spec]
    simp [f]
  have hmapInv : Units.map f.toMonoidHom (hdK.unit⁻¹) = hdM.unit⁻¹ := by
    rw [map_inv, hmapUnit]
  change f ((r.num : ZMod K) * ↑(hdK.unit⁻¹)) =
    (r.num : ZMod M) * ↑(hdM.unit⁻¹)
  rw [map_mul]
  rw [show f (r.num : ZMod K) = (r.num : ZMod M) by simp [f]]
  rw [show f (↑(hdK.unit⁻¹) : ZMod K) =
      ↑(Units.map f.toMonoidHom hdK.unit⁻¹) by rfl]
  rw [hmapInv]

private def rationalRowDenominator {d : ℕ} (rows : Fin d → ℚ) : ℕ :=
  ∏ j, (rows j).den

private def rationalRowDenominatorExcept {d : ℕ} (rows : Fin d → ℚ)
    (j : Fin d) : ℕ :=
  ∏ k ∈ Finset.univ.erase j, (rows k).den

private def rationalRowClearedCoefficient {d : ℕ} (rows : Fin d → ℚ)
    (j : Fin d) : ℤ :=
  (rows j).num * (rationalRowDenominatorExcept rows j : ℤ)

private theorem rationalRowDenominator_factor {d : ℕ} (rows : Fin d → ℚ) (j : Fin d) :
    rationalRowDenominator rows =
      (rows j).den * rationalRowDenominatorExcept rows j := by
  classical
  dsimp [rationalRowDenominator, rationalRowDenominatorExcept]
  exact (Finset.mul_prod_erase Finset.univ (fun k => (rows k).den)
    (Finset.mem_univ j)).symm

private theorem rationalRow_coefficient_clearDenominator {d : ℕ}
    (rows : Fin d → ℚ) (j : Fin d) :
    (rationalRowDenominator rows : ℚ) * rows j =
      (rationalRowClearedCoefficient rows j : ℚ) := by
  have hnum : ((rows j).den : ℚ) * rows j = (rows j).num := by
    calc
      ((rows j).den : ℚ) * rows j =
          (rows j).den * ((rows j).num / (rows j).den) := by
            rw [(rows j).num_div_den]
      _ = (rows j).num := by
        have hden : (0 : ℚ) < (rows j).den := by exact_mod_cast Rat.den_pos (rows j)
        field_simp [ne_of_gt hden]
  unfold rationalRowClearedCoefficient
  rw [rationalRowDenominator_factor]
  push_cast
  calc
    (rows j).den * (rationalRowDenominatorExcept rows j : ℚ) * rows j =
        (rationalRowDenominatorExcept rows j : ℚ) *
          ((rows j).den : ℚ) * rows j := by ring
    _ = (rationalRowDenominatorExcept rows j : ℚ) * (rows j).num := by
      calc
        _ = (rationalRowDenominatorExcept rows j : ℚ) *
            (((rows j).den : ℚ) * rows j) := by ring
        _ = (rationalRowDenominatorExcept rows j : ℚ) * (rows j).num :=
          congrArg (fun z : ℚ => (rationalRowDenominatorExcept rows j : ℚ) * z) hnum
    _ = (((rows j).num : ℤ) *
          (rationalRowDenominatorExcept rows j : ℤ) : ℚ) := by
      norm_cast
      ring

private theorem rationalRow_commonDenominator_value {d : ℕ}
    (rows : Fin d → ℚ) (x : Fin d → ℤ) :
    (rationalRowDenominator rows : ℚ) *
        (∑ j, rows j * (x j : ℚ)) =
      ∑ j, (rationalRowClearedCoefficient rows j : ℚ) * (x j : ℚ) := by
  calc
    (rationalRowDenominator rows : ℚ) *
        (∑ j, rows j * (x j : ℚ)) =
      ∑ j, (rationalRowDenominator rows : ℚ) *
        (rows j * (x j : ℚ)) := by rw [Finset.mul_sum]
    _ = ∑ j, ((rationalRowDenominator rows : ℚ) * rows j) * (x j : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j, (rationalRowClearedCoefficient rows j : ℚ) * (x j : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rationalRow_coefficient_clearDenominator]

private theorem rationalRow_commonDenominator_value_int {d : ℕ}
    (rows : Fin d → ℚ) (x : Fin d → ℤ)
    (hden : (∑ j, rows j * (x j : ℚ)).den = 1) :
    (rationalRowDenominator rows : ℤ) * (∑ j, rows j * (x j : ℚ)).num =
      ∑ j, rationalRowClearedCoefficient rows j * x j := by
  let R : ℚ := ∑ j, rows j * (x j : ℚ)
  have hRcast : (R.num : ℚ) = R := (Rat.den_eq_one_iff R).mp (by simpa [R] using hden)
  have hQ : (((rationalRowDenominator rows : ℤ) * R.num : ℤ) : ℚ) =
      ((∑ j, rationalRowClearedCoefficient rows j * x j : ℤ) : ℚ) := by
    calc
      (((rationalRowDenominator rows : ℤ) * R.num : ℤ) : ℚ) =
          (rationalRowDenominator rows : ℚ) * (R.num : ℚ) := by norm_cast
      _ = (rationalRowDenominator rows : ℚ) * R := by rw [hRcast]
      _ = ∑ j, (rationalRowClearedCoefficient rows j : ℚ) * (x j : ℚ) := by
        dsimp [R]
        exact rationalRow_commonDenominator_value rows x
      _ = ((∑ j, rationalRowClearedCoefficient rows j * x j : ℤ) : ℚ) := by
        simp only [Int.cast_sum, Int.cast_mul]
  exact_mod_cast hQ

private theorem rationalRow_cleared_modulus_divisibility {d K σ : ℕ}
    (hdiv : σ ∣ K) (rows : Fin d → ℚ) (x : Fin d → ℤ)
    (xmod : Fin d → ZMod K) (hxmod : ∀ j, xmod j = (x j : ZMod K))
    (hDcop : Nat.Coprime (rationalRowDenominator rows) σ)
    (hRden : (∑ j, rows j * (x j : ℚ)).den = 1) :
    (ZMod.castHom hdiv (ZMod σ)
      (∑ j, (rationalRowClearedCoefficient rows j : ZMod K) * xmod j) = 0) ↔
      (σ : ℤ) ∣ (∑ j, rows j * (x j : ℚ)).num := by
  classical
  let f : ZMod K →+* ZMod σ := ZMod.castHom hdiv (ZMod σ)
  let R : ℚ := ∑ j, rows j * (x j : ℚ)
  let Dden : ℕ := rationalRowDenominator rows
  have hInt := rationalRow_commonDenominator_value_int rows x hRden
  have hmodK : (Dden : ZMod K) * (R.num : ZMod K) =
      ∑ j, (rationalRowClearedCoefficient rows j : ZMod K) * xmod j := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod K)) hInt
    have hxmod' (j : Fin d) : (x j : ZMod K) = xmod j := (hxmod j).symm
    dsimp [Dden, R] at hcast ⊢
    simpa only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, hxmod'] using hcast
  have hmodσ : (Dden : ZMod σ) * (R.num : ZMod σ) =
      f (∑ j, (rationalRowClearedCoefficient rows j : ZMod K) * xmod j) := by
    calc
      _ = f (Dden : ZMod K) * f (R.num : ZMod K) := by simp [f]
      _ = f ((Dden : ZMod K) * (R.num : ZMod K)) :=
        (map_mul f (Dden : ZMod K) (R.num : ZMod K)).symm
      _ = f (∑ j, (rationalRowClearedCoefficient rows j : ZMod K) * xmod j) :=
        congrArg f hmodK
  have hDunit : IsUnit (Dden : ZMod σ) :=
    (ZMod.isUnit_iff_coprime Dden σ).2 hDcop
  constructor
  · intro hzero
    have hmul : (Dden : ZMod σ) * (R.num : ZMod σ) = 0 := by
      rw [hmodσ]
      exact hzero
    have hnumzero : (R.num : ZMod σ) = 0 := by
      have hval : (↑(hDunit.unit⁻¹) : ZMod σ) * ↑hDunit.unit = 1 := by
        simpa using Units.inv_val hDunit.unit
      calc
        (R.num : ZMod σ) = 1 * (R.num : ZMod σ) := by simp
        _ = (↑(hDunit.unit⁻¹) : ZMod σ) *
            (↑hDunit.unit : ZMod σ) * (R.num : ZMod σ) := by rw [hval]
        _ = (↑(hDunit.unit⁻¹) : ZMod σ) *
            ((Dden : ZMod σ) * (R.num : ZMod σ)) := by
              rw [hDunit.unit_spec]
              ring
        _ = 0 := by rw [hmul]; simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hnumzero
  · intro hdivNum
    have hnumzero : (R.num : ZMod σ) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdivNum
    rw [← hmodσ, hnumzero, mul_zero]

private theorem zmod_int_mul (M : ℕ) (a b : ℤ) :
    (a : ZMod M) * (b : ZMod M) = ((a * b : ℤ) : ZMod M) := by
  exact (Int.cast_mul (α := ZMod M) a b).symm

private theorem rationalRow_clearedCoefficient_modulus {d M : ℕ}
    (rows : Fin d → ℚ) (hden : ∀ j, Nat.Coprime (rows j).den M) (j : Fin d) :
    (rationalRowDenominator rows : ZMod M) *
        rationalResidueModulus M (rows j) (hden j) =
      (rationalRowClearedCoefficient rows j : ZMod M) := by
  classical
  let hd : IsUnit ((rows j).den : ZMod M) :=
    (ZMod.isUnit_iff_coprime (rows j).den M).2 (hden j)
  have hfactor : (rows j).den * rationalRowDenominatorExcept rows j =
      rationalRowDenominator rows := by
    dsimp [rationalRowDenominator, rationalRowDenominatorExcept]
    exact Finset.mul_prod_erase Finset.univ (fun k => (rows k).den)
      (Finset.mem_univ j)
  have hfactorZ :
      ((rows j).den : ZMod M) *
        (rationalRowDenominatorExcept rows j : ZMod M) =
      (rationalRowDenominator rows : ZMod M) := by
    calc
      _ = (((rows j).den * rationalRowDenominatorExcept rows j : ℕ) : ZMod M) := by
        change ((rows j).den : ZMod M) *
          (rationalRowDenominatorExcept rows j : ZMod M) =
            (((rows j).den * rationalRowDenominatorExcept rows j : ℕ) : ZMod M)
        simp [Nat.cast_mul]
      _ = (rationalRowDenominator rows : ZMod M) :=
        congrArg (fun n : ℕ => (n : ZMod M)) hfactor
  have hunit : ((rows j).den : ZMod M) * ↑(hd.unit⁻¹) = 1 := by
    calc
      (rows j).den * ↑(hd.unit⁻¹) = (↑hd.unit : ZMod M) * ↑(hd.unit⁻¹) := by
        rw [hd.unit_spec]
      _ = 1 := by simpa using Units.val_inv hd.unit
  have hrr : rationalResidueModulus M (rows j) (hden j) =
      (rows j).num * ↑(hd.unit⁻¹) := rfl
  rw [hrr]
  unfold rationalRowClearedCoefficient
  calc
    (rationalRowDenominator rows : ZMod M) *
        (((rows j).num : ZMod M) * ↑(hd.unit⁻¹)) =
      ((rows j).den : ZMod M) *
        (rationalRowDenominatorExcept rows j : ZMod M) *
        ((rows j).num : ZMod M) * ↑(hd.unit⁻¹) := by
          rw [← hfactorZ]
          ring
    _ = (rows j).num * (rationalRowDenominatorExcept rows j : ZMod M) *
          (((rows j).den : ZMod M) * ↑(hd.unit⁻¹)) := by ring
    _ = (rows j).num * (rationalRowDenominatorExcept rows j : ZMod M) * 1 := by
      rw [hunit]
    _ = (rows j).num * (rationalRowDenominatorExcept rows j : ZMod M) := by simp
    _ = ((((rows j).num : ℤ) *
          (rationalRowDenominatorExcept rows j : ℤ) : ℤ) : ZMod M) := by
      have hden : (rationalRowDenominatorExcept rows j : ZMod M) =
          ((rationalRowDenominatorExcept rows j : ℤ) : ZMod M) :=
        (Int.cast_natCast (R := ZMod M) (rationalRowDenominatorExcept rows j)).symm
      calc
        _ = (rows j).num *
            ((rationalRowDenominatorExcept rows j : ℤ) : ZMod M) :=
          congrArg (fun z : ZMod M => (rows j).num * z) hden
        _ = ((((rows j).num : ℤ) *
            (rationalRowDenominatorExcept rows j : ℤ) : ℤ) : ZMod M) := by
          exact zmod_int_mul M (rows j).num
            (rationalRowDenominatorExcept rows j : ℤ)

/-- Rational coefficient reduced modulo a prime power when its denominator is a unit. -/
noncomputable def rationalResidueModPow (p a : ℕ) (r : ℚ)
    (hden : Nat.Coprime r.den (p ^ a)) : ZMod (p ^ a) := by
  let hd : IsUnit (r.den : ZMod (p ^ a)) :=
    (ZMod.isUnit_iff_coprime r.den (p ^ a)).2 hden
  exact (r.num : ZMod (p ^ a)) * ↑(hd.unit⁻¹)

private theorem rationalResidueModPow_cast {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (r : ℚ) (hden : Nat.Coprime r.den (p ^ a)) :
    (ZMod.castHom (m := p) (n := p ^ a) (by
      simpa using (Nat.pow_dvd_pow (m := 1) (n := a) p (by omega : 1 ≤ a)))
        (ZMod p))
        (rationalResidueModPow p a r hden) = rationalResidue p hp r := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hpdiv : p ∣ p ^ a := by
    simpa using (Nat.pow_dvd_pow (m := 1) (n := a) p (by omega : 1 ≤ a))
  let f : ZMod (p ^ a) →+* ZMod p :=
    ZMod.castHom (m := p) (n := p ^ a) hpdiv (ZMod p)
  have hdenP : Nat.Coprime r.den p := hden.coprime_dvd_right hpdiv
  have hdK : IsUnit (r.den : ZMod (p ^ a)) :=
    (ZMod.isUnit_iff_coprime r.den (p ^ a)).2 hden
  have hdP : IsUnit (r.den : ZMod p) :=
    (ZMod.isUnit_iff_coprime r.den p).2 hdenP
  have hmapUnit : Units.map f.toMonoidHom hdK.unit = hdP.unit := by
    apply Units.ext
    change f (↑hdK.unit) = ↑hdP.unit
    rw [hdK.unit_spec, hdP.unit_spec]
    simp [f]
  have hmapInv : Units.map f.toMonoidHom (hdK.unit⁻¹) = hdP.unit⁻¹ := by
    rw [map_inv, hmapUnit]
  change f ((r.num : ZMod (p ^ a)) * ↑(hdK.unit⁻¹)) = _
  rw [map_mul]
  rw [show f (r.num : ZMod (p ^ a)) = (r.num : ZMod p) by simp [f]]
  rw [show f (↑(hdK.unit⁻¹) : ZMod (p ^ a)) =
      ↑(Units.map f.toMonoidHom hdK.unit⁻¹) by rfl]
  rw [hmapInv]
  have hInv : (↑hdP.unit⁻¹ : ZMod p) = (r.den : ZMod p)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hdP.unit_spec]
  rw [hInv]
  simp [rationalResidue, div_eq_mul_inv]

private theorem zmodPrimePower_isUnit_of_cast_ne_zero {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (x : ZMod (p ^ a))
    (hcast : (ZMod.castHom (m := p) (n := p ^ a) (by
      simpa using (Nat.pow_dvd_pow (m := 1) (n := a) p (by omega : 1 ≤ a)))
        (ZMod p)) x ≠ 0) : IsUnit x := by
  let f : ZMod (p ^ a) →+* ZMod p := ZMod.castHom (m := p) (n := p ^ a)
    (by simpa using (Nat.pow_dvd_pow (m := 1) (n := a) p (by omega : 1 ≤ a)))
    (ZMod p)
  letI : NeZero (p ^ a) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  have hcastVal : f x = (x.val : ZMod p) := by
    rw [← ZMod.natCast_zmod_val x]
    simp [f]
  have hval : (x.val : ZMod p) ≠ 0 := by
    have hcast' : f x ≠ 0 := by simpa [f] using hcast
    rw [hcastVal] at hcast'
    exact hcast'
  have hnot : ¬ p ∣ x.val := by
    intro hdvd
    apply hval
    exact (ZMod.natCast_eq_zero_iff x.val p).2 hdvd
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).2 hnot

private theorem rationalResidueModPow_isUnit {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (r : ℚ) (hden : Nat.Coprime r.den (p ^ a))
    (hres : rationalResidue p hp r ≠ 0) :
    IsUnit (rationalResidueModPow p a r hden) :=
  zmodPrimePower_isUnit_of_cast_ne_zero hp ha _ (by
    rw [rationalResidueModPow_cast hp ha r hden]
    exact hres)

private def rationalRowsModPow {p A q d : ℕ}
    (rows : Fin q → Fin d → ℚ)
    (hden : ∀ u j, Nat.Coprime (rows u j).den p) :
    Fin q → Fin d → ZMod (p ^ A) := fun u j =>
  rationalResidueModPow p A (rows u j)
    (Nat.Coprime.pow_right A (hden u j))

private theorem rationalResidueModulus_cast_pow {K p A : ℕ}
    (hpow : p ^ A ∣ K) (r : ℚ) (hden : Nat.Coprime r.den K) :
    ZMod.castHom hpow (ZMod (p ^ A)) (rationalResidueModulus K r hden) =
      rationalResidueModPow p A r (hden.coprime_dvd_right hpow) := by
  rw [rationalResidueModulus_cast hpow r hden (hden.coprime_dvd_right hpow)]
  rfl

private theorem rationalRowsModPow_row_unit {p A q d : ℕ} (hp : p.Prime)
    (hA : 0 < A) (rows : Fin q → Fin d → ℚ)
    (hden : ∀ u j, Nat.Coprime (rows u j).den p)
    (u : Fin q) (hrow : ∃ j, rationalResidue p hp (rows u j) ≠ 0) :
    ∃ j, IsUnit (rationalRowsModPow (p := p) (A := A) rows hden u j) := by
  obtain ⟨j, hj⟩ := hrow
  exact ⟨j, rationalResidueModPow_isUnit hp hA (rows u j)
    (Nat.Coprime.pow_right A (hden u j)) hj⟩

private theorem rationalRowsModPow_minor_unit {p A q d : ℕ} (hp : p.Prime)
    (hA : 0 < A) (rows : Fin q → Fin d → ℚ)
    (hden : ∀ u j, Nat.Coprime (rows u j).den p)
    (u v : Fin q) (i j : Fin d)
    (hminor : rationalResidue p hp (rows u i) * rationalResidue p hp (rows v j) ≠
      rationalResidue p hp (rows u j) * rationalResidue p hp (rows v i)) :
    IsUnit (rationalRowsModPow (p := p) (A := A) rows hden u i *
      rationalRowsModPow (p := p) (A := A) rows hden v j -
      rationalRowsModPow (p := p) (A := A) rows hden u j *
        rationalRowsModPow (p := p) (A := A) rows hden v i) := by
  let det := rationalRowsModPow (p := p) (A := A) rows hden u i *
      rationalRowsModPow (p := p) (A := A) rows hden v j -
      rationalRowsModPow (p := p) (A := A) rows hden u j *
        rationalRowsModPow (p := p) (A := A) rows hden v i
  have hcast :
      (ZMod.castHom (m := p) (n := p ^ A) (by
        simpa using (Nat.pow_dvd_pow (m := 1) (n := A) p (by omega : 1 ≤ A)))
        (ZMod p)) det =
        rationalResidue p hp (rows u i) * rationalResidue p hp (rows v j) -
          rationalResidue p hp (rows u j) * rationalResidue p hp (rows v i) := by
    let f : ZMod (p ^ A) →+* ZMod p := ZMod.castHom (m := p) (n := p ^ A)
      (by simpa using (Nat.pow_dvd_pow (m := 1) (n := A) p (by omega : 1 ≤ A)))
      (ZMod p)
    have hUI : (rationalResidueModPow p A (rows u i)
        (Nat.Coprime.pow_right A (hden u i))).cast = rationalResidue p hp (rows u i) := by
      simpa only [ZMod.castHom_apply] using rationalResidueModPow_cast hp hA (rows u i)
        (Nat.Coprime.pow_right A (hden u i))
    have hVJ : (rationalResidueModPow p A (rows v j)
        (Nat.Coprime.pow_right A (hden v j))).cast = rationalResidue p hp (rows v j) := by
      simpa only [ZMod.castHom_apply] using rationalResidueModPow_cast hp hA (rows v j)
        (Nat.Coprime.pow_right A (hden v j))
    have hUJ : (rationalResidueModPow p A (rows u j)
        (Nat.Coprime.pow_right A (hden u j))).cast = rationalResidue p hp (rows u j) := by
      simpa only [ZMod.castHom_apply] using rationalResidueModPow_cast hp hA (rows u j)
        (Nat.Coprime.pow_right A (hden u j))
    have hVI : (rationalResidueModPow p A (rows v i)
        (Nat.Coprime.pow_right A (hden v i))).cast = rationalResidue p hp (rows v i) := by
      simpa only [ZMod.castHom_apply] using rationalResidueModPow_cast hp hA (rows v i)
        (Nat.Coprime.pow_right A (hden v i))
    calc
      _ = f det := rfl
      _ = f (rationalRowsModPow (p := p) (A := A) rows hden u i) *
          f (rationalRowsModPow (p := p) (A := A) rows hden v j) -
          f (rationalRowsModPow (p := p) (A := A) rows hden u j) *
          f (rationalRowsModPow (p := p) (A := A) rows hden v i) := by
            dsimp [det]
            rw [map_sub, map_mul, map_mul]
      _ = _ := by
        dsimp [f, rationalRowsModPow]
        rw [hUI, hVJ, hUJ, hVI]
  apply zmodPrimePower_isUnit_of_cast_ne_zero hp hA det
  rw [hcast]
  exact sub_ne_zero.mpr hminor

private abbrev primePowerIndex (K : ℕ) := {p : ℕ // p ∈ K.primeFactors}

private def primePowerModuli (K : ℕ) : primePowerIndex K → ℕ :=
  fun p => p.val ^ K.factorization p.val

private theorem primePowerIndex_prime {K : ℕ} (p : primePowerIndex K) : p.val.Prime := by
  exact Nat.prime_of_mem_primeFactors p.property

private theorem primePowerModuli_pairwise_coprime (K : ℕ) :
    Pairwise (Function.onFun Nat.Coprime (primePowerModuli K)) := by
  change Pairwise (Function.onFun Nat.Coprime
    (fun p : {p : ℕ // p ∈ K.primeFactors} => p.val ^ K.factorization p.val))
  exact Nat.pairwise_coprime_pow_primeFactors_factorization

private theorem primePowerFamily_pairwise_coprime {K : ℕ}
    (e : primePowerIndex K → ℕ) :
    Pairwise (Function.onFun Nat.Coprime (fun p => p.val ^ e p)) := by
  intro p q hpq
  have hp : p.val.Prime := primePowerIndex_prime p
  have hq : q.val.Prime := primePowerIndex_prime q
  have hnot : ¬ p.val ∣ q.val := by
    intro hd
    have heq := (hq.dvd_iff_eq hp.ne_one).mp hd
    exact hpq (Subtype.ext heq.symm)
  have hcop : Nat.Coprime p.val q.val := hp.coprime_iff_not_dvd.mpr hnot
  exact Nat.Coprime.pow_left (e p) (Nat.Coprime.pow_right (e q) hcop)

private theorem primePowerModuli_prod (K : ℕ) (hK : K ≠ 0) :
    ∏ p : primePowerIndex K, primePowerModuli K p = K := by
  classical
  simpa [primePowerIndex, primePowerModuli] using
    (Nat.prod_primeFactors_coe_pow_factorization (n := K) hK).symm

private theorem rowPrimePowerProduct_eq {K σ : ℕ}
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hdiv : σ ∣ K) :
    ∏ p : primePowerIndex K, p.val ^ σ.factorization p.val = σ := by
  classical
  have hsubset : σ.primeFactors ⊆ K.primeFactors := by
    intro p hp
    have hp' := (Nat.mem_primeFactors.mp hp)
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, dvd_trans hp'.2.1 hdiv, hK⟩
  have hsubtype :
      (∏ p : primePowerIndex K, p.val ^ σ.factorization p.val) =
        ∏ p ∈ K.primeFactors, p ^ σ.factorization p := by
    simpa [primePowerIndex] using
      (Finset.prod_subtype (s := K.primeFactors)
        (h := fun p => Iff.rfl) (f := fun p => p ^ σ.factorization p)).symm
  calc
    (∏ p : primePowerIndex K, p.val ^ σ.factorization p.val) =
        ∏ p ∈ K.primeFactors, p ^ σ.factorization p := hsubtype
    _ = ∏ p ∈ σ.primeFactors, p ^ σ.factorization p := by
      symm
      apply Finset.prod_subset hsubset
      intro p hpK hpNot
      have hnotSupp : p ∉ σ.factorization.support := by
        simpa [Nat.support_factorization] using hpNot
      have hzero : σ.factorization p = 0 := by
        by_contra hn
        exact hnotSupp (Finsupp.mem_support_iff.mpr hn)
      simp [hzero]
    _ = ∏ p : σ.primeFactors, p.val ^ σ.factorization p.val := by
      exact Finset.prod_subtype σ.primeFactors (fun p => Iff.rfl)
        (fun p => p ^ σ.factorization p)
    _ = σ := (Nat.prod_primeFactors_coe_pow_factorization (n := σ) hσ).symm

private noncomputable def primePowerCRTRingEquiv (K : ℕ) (hK : K ≠ 0) :
    ZMod K ≃+* ((p : primePowerIndex K) → ZMod (primePowerModuli K p)) := by
  let hprod := primePowerModuli_prod K hK
  exact (RingEquiv.cast (R := fun n : ℕ => ZMod n) hprod.symm).trans
    (ZMod.prodEquivPi (primePowerModuli K) (primePowerModuli_pairwise_coprime K))

private noncomputable def rowPrimePowerCRTRingEquiv {K σ : ℕ}
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hdiv : σ ∣ K) :
    ZMod σ ≃+* ((p : primePowerIndex K) → ZMod (p.val ^ σ.factorization p.val)) := by
  let exponents : primePowerIndex K → ℕ := fun p => σ.factorization p.val
  let moduli : primePowerIndex K → ℕ := fun p => p.val ^ exponents p
  have hprod : ∏ p : primePowerIndex K, moduli p = σ := by
    simpa [exponents, moduli] using rowPrimePowerProduct_eq hσ hK hdiv
  exact (RingEquiv.cast (R := fun n : ℕ => ZMod n) hprod.symm).trans
    (ZMod.prodEquivPi moduli (primePowerFamily_pairwise_coprime exponents))

private theorem zmodRingEquivCast_apply {n m : ℕ} (h : n = m) (x : ZMod n) :
    (RingEquiv.cast (R := fun k : ℕ => ZMod k) h) x =
      ZMod.castHom (dvd_of_eq h.symm) (ZMod m) x := by
  cases h
  simp

private theorem primePowerCRTRingEquiv_apply {K : ℕ} (hK : K ≠ 0)
    (x : ZMod K) (p : primePowerIndex K) :
    primePowerCRTRingEquiv K hK x p =
    ZMod.castHom (m := primePowerModuli K p) (n := K) (by
        have hp := primePowerIndex_prime p
        exact (hp.pow_dvd_iff_le_factorization hK).2 le_rfl)
        (ZMod (primePowerModuli K p)) x := by
  let hprod := primePowerModuli_prod K hK
  have hmodProd : primePowerModuli K p ∣ ∏ p, primePowerModuli K p :=
    Finset.dvd_prod_of_mem (fun r : primePowerIndex K => primePowerModuli K r)
      (Finset.mem_univ p)
  change (ZMod.prodEquivPi (primePowerModuli K) (primePowerModuli_pairwise_coprime K))
      ((RingEquiv.cast (R := fun n : ℕ => ZMod n) hprod.symm) x) p = _
  rw [ZMod.prodEquivPi_apply, zmodRingEquivCast_apply hprod.symm]
  change ((ZMod.castHom hmodProd (ZMod (primePowerModuli K p))).comp
      (ZMod.castHom (dvd_of_eq hprod)
        (ZMod (∏ p, primePowerModuli K p)))) x = _
  exact congrArg (fun f : ZMod K →+* ZMod (primePowerModuli K p) => f x)
    (ZMod.castHom_comp (n := primePowerModuli K p) hmodProd (dvd_of_eq hprod))

private theorem rowPrimePowerCRTRingEquiv_apply {K σ : ℕ}
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hdiv : σ ∣ K)
    (x : ZMod σ) (p : primePowerIndex K) :
    rowPrimePowerCRTRingEquiv hσ hK hdiv x p =
      ZMod.castHom (m := p.val ^ σ.factorization p.val) (n := σ) (by
        have hp := primePowerIndex_prime p
        exact (hp.pow_dvd_iff_le_factorization hσ).2 le_rfl)
        (ZMod (p.val ^ σ.factorization p.val)) x := by
  let exponents : primePowerIndex K → ℕ := fun p => σ.factorization p.val
  let moduli : primePowerIndex K → ℕ := fun p => p.val ^ exponents p
  have hprod := rowPrimePowerProduct_eq hσ hK hdiv
  have hmodProd : p.val ^ σ.factorization p.val ∣
      ∏ p : primePowerIndex K, moduli p :=
    Finset.dvd_prod_of_mem moduli (Finset.mem_univ p)
  change (ZMod.prodEquivPi moduli (primePowerFamily_pairwise_coprime exponents))
      ((RingEquiv.cast (R := fun n : ℕ => ZMod n) hprod.symm) x) p = _
  rw [ZMod.prodEquivPi_apply, zmodRingEquivCast_apply hprod.symm]
  change ((ZMod.castHom hmodProd
        (ZMod (p.val ^ σ.factorization p.val))).comp
      (ZMod.castHom (dvd_of_eq hprod)
        (ZMod (∏ p : primePowerIndex K, moduli p)))) x = _
  exact congrArg (fun f : ZMod σ →+* ZMod (p.val ^ σ.factorization p.val) => f x)
    (ZMod.castHom_comp (n := p.val ^ σ.factorization p.val) hmodProd
      (dvd_of_eq hprod))

private def piSwapRingEquiv {α β : Type*} (R : α → β → Type*)
    [∀ a b, CommSemiring (R a b)] :
    ((a : α) → (b : β) → R a b) ≃+* ((b : β) → (a : α) → R a b) where
  toFun := fun x b a => x a b
  invFun := fun x a b => x b a
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_mul' := by intro x y; rfl
  map_add' := by intro x y; rfl

private noncomputable def primePowerCRTVectorEquiv (K d : ℕ) (hK : K ≠ 0) :
    (Fin d → ZMod K) ≃+*
      ((p : primePowerIndex K) → Fin d → ZMod (primePowerModuli K p)) := by
  exact (RingEquiv.piCongrRight
      (fun _ : Fin d => primePowerCRTRingEquiv K hK)).trans
    (piSwapRingEquiv (fun (_ : Fin d) (p : primePowerIndex K) =>
      ZMod (primePowerModuli K p)))

private noncomputable def rowPrimePowerCRTVectorEquiv {K q : ℕ}
    (σ : Fin q → ℕ) (hσ : ∀ u, σ u ≠ 0) (hK : K ≠ 0)
    (hdiv : ∀ u, σ u ∣ K) :
    ((u : Fin q) → ZMod (σ u)) ≃+*
      ((p : primePowerIndex K) → (u : Fin q) →
        ZMod (p.val ^ (σ u).factorization p.val)) := by
  let rowCRT : (u : Fin q) → ZMod (σ u) ≃+*
      ((p : primePowerIndex K) → ZMod (p.val ^ (σ u).factorization p.val)) :=
    fun u => rowPrimePowerCRTRingEquiv (hσ u) hK (hdiv u)
  exact (RingEquiv.piCongrRight rowCRT).trans
    (piSwapRingEquiv (fun (u : Fin q) (p : primePowerIndex K) =>
      ZMod (p.val ^ (σ u).factorization p.val)))

/-- A row coefficient reduced modulo p. -/
noncomputable def rationalRowCoefficientResidue {d m : ℕ}
    (L : RationalLinearRow d m) (p : ℕ) (hp : p.Prime)
    (slots : Fin m → ℕ) (j : Fin d) : ZMod p :=
  rationalResidue p hp (rationalRowCoefficient L slots j)

/-- A row is primitive modulo p when its coefficient vector is nonzero. -/
def rowPrimitiveModulo {d m : ℕ} (L : RationalLinearRow d m)
    (p : ℕ) (hp : p.Prime) (slots : Fin m → ℕ) : Prop :=
  ∃ j, rationalRowCoefficientResidue L p hp slots j ≠ 0

/-- Two rows are linearly independent modulo p, expressed by a nonzero two-column minor. -/
def rowsIndependentModulo {d m : ℕ} (L₁ L₂ : RationalLinearRow d m)
    (p : ℕ) (hp : p.Prime) (slots : Fin m → ℕ) : Prop :=
  ∃ i j,
    rationalRowCoefficientResidue L₁ p hp slots i *
        rationalRowCoefficientResidue L₂ p hp slots j ≠
      rationalRowCoefficientResidue L₁ p hp slots j *
        rationalRowCoefficientResidue L₂ p hp slots i

/-- A product of at most b independent raw harmonic W-unit variables, identified by their
master cutoffs. -/
structure DivisorTemplate (n b : ℕ) where
  arity : ℕ
  arity_le : arity ≤ b
  cutoff : Fin arity → Fin n

/-- Divisor law for one fresh occurrence of a weight, at the parameter cutoffs. -/
def divisorTemplateLaw {n b : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (D : DivisorTemplate n b) (σ : ℕ) : ℝ :=
  harmonicProductLaw (primorial (N + 1))
    (fun i => A.X N (D.cutoff i)) σ

/-- CRT residue vectors for all primes `w<p≤V`, with residues in their prime fields. -/
abbrev CRTPrimeRange (w V : ℕ) :=
  {p : ℕ // p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime}

/-- Residues modulo each prime in the CRT range. -/
abbrev CRTResidues (w V : ℕ) := ∀ p : CRTPrimeRange w V, Fin p.val

/-- CRT residue tuple of one integer. -/
noncomputable def integerCRTResidues (w V x : ℕ) : CRTResidues w V := by
  intro p
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  exact ⟨x % p.val, Nat.mod_lt _ hp.pos⟩

/-- Actual joint CRT law of independent prime slots from their assigned pools. -/
def primeTupleCRTLaw {m : ℕ} (lo hi : Fin m → ℕ) (w V : ℕ)
    (r : Fin m → CRTResidues w V) : ℝ :=
  ∑' p : Fin m → ℕ,
    independentPrimePoolMass lo hi p *
      if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0

/-- Independent uniform unit law on all slot-prime CRT coordinates. -/
def uniformPrimeTupleCRTLaw {m : ℕ} (w V : ℕ)
    (r : Fin m → CRTResidues w V) : ℝ :=
  ∏ i, ∏ p : CRTPrimeRange w V,
    if Nat.Coprime (r i p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0

/-- Integer residue in `Fin K`, using Euclidean remainder for signed base variables. -/
def integerResidue (K : ℕ) (hK : 0 < K) (z : ℤ) : Fin K := by
  have hKz : (0 : ℤ) < (K : ℤ) := by exact_mod_cast hK
  have hz0 : 0 ≤ z % (K : ℤ) := Int.emod_nonneg z (Int.ne_of_gt hKz)
  have hzlt : z % (K : ℤ) < (K : ℤ) := Int.emod_lt_of_pos z hKz
  refine ⟨(z % (K : ℤ)).toNat, ?_⟩
  have hcast : (((z % (K : ℤ)).toNat : ℕ) : ℤ) = z % (K : ℤ) :=
    Int.toNat_of_nonneg hz0
  exact Nat.cast_lt.mp (by rw [hcast]; exact hzlt)

private theorem integerResidue_finEquiv {K : ℕ} (hK : 0 < K) (z : ℤ) :
    (@ZMod.finEquiv K ⟨Nat.ne_of_gt hK⟩) (integerResidue K hK z) = (z : ZMod K) := by
  classical
  cases K with
  | zero => omega
  | succ K =>
      letI : NeZero (K + 1) := ⟨by omega⟩
      change integerResidue (K + 1) hK z = (z : ZMod (K + 1))
      apply Fin.ext
      change (z % ((K + 1 : ℕ) : ℤ)).toNat = (z : ZMod (K + 1)).val
      have hKz : (0 : ℤ) < ((K + 1 : ℕ) : ℤ) := by exact_mod_cast (Nat.zero_lt_succ K)
      have hz0 : 0 ≤ z % ((K + 1 : ℕ) : ℤ) :=
        Int.emod_nonneg z (Int.ne_of_gt hKz)
      have htoNat :
          (((z % ((K + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
            z % ((K + 1 : ℕ) : ℤ) := Int.toNat_of_nonneg hz0
      have hval : ((z : ZMod (K + 1)).val : ℤ) =
          z % ((K + 1 : ℕ) : ℤ) := ZMod.val_intCast z
      exact_mod_cast htoNat.trans hval.symm

/-- Conditional residue mass of the base variables modulo a divisor product. -/
def baseResidueLaw {d : ℕ} (K : ℕ) (hK : 0 < K)
    (baseMass : (Fin d → ℤ) → ℝ) (r : Fin d → Fin K) : ℝ :=
  ∑' x : Fin d → ℤ,
    baseMass x * if (fun i => integerResidue K hK (x i)) = r then 1 else 0

/-- Uniform law on all residue vectors modulo K. -/
def uniformBaseResidueLaw (K d : ℕ) (_r : Fin d → Fin K) : ℝ :=
  1 / (K : ℝ) ^ d

/-- Complete data and hypotheses for the weighted linear-forms proposition. The divisor
templates are fresh independent raw harmonic draws for each row occurrence. -/
structure WeightedLinearFormsData {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    (S : MasterScales n Aset m tests) where
  gap : Fin m → Fin n
  rowCoeff : ℕ → (Fin m → ℕ) → Fin q → Fin d → ℚ
  divisor : Fin q → DivisorTemplate n b
  V : ℕ → ℕ
  epsilonBase : ℕ → ℝ
  epsilonCRT : ℕ → ℝ
  baseMass : ℕ → (Fin m → ℕ) → (Fin d → ℤ) → ℝ
  goodDomain : ℕ → (Fin m → ℕ) → Prop
  epsilonBase_nonnegative : ∀ N, 0 ≤ epsilonBase N
  V_lower : ∀ N, S.core.parameters.M N ≤ V N
  V_tendsto : Tendsto (fun N => V N) atTop atTop
  slot_gap_bound : ∀ N i, V N ≤ masterScaleV S.core.parameters N (gap i)
  base_nonnegative : ∀ N p x, 0 ≤ baseMass N p x
  base_normalized : ∀ N p, ∑' x : Fin d → ℤ, baseMass N p x = 1
  divisor_positive : ∀ N u σ, divisorTemplateLaw S.core.parameters N (divisor u) σ ≠ 0 → 1 ≤ σ
  divisor_bounded : ∀ N u σ,
    divisorTemplateLaw S.core.parameters N (divisor u) σ ≠ 0 → σ ≤ V N
  base_residue_uniform : ∀ N p (σ : Fin q → ℕ),
    goodDomain N p →
    (∀ u, divisorTemplateLaw S.core.parameters N (divisor u) (σ u) ≠ 0) →
    (hσ : ∀ u, 0 < σ u) →
    finiteL1
      (baseResidueLaw (∏ u, σ u) (by exact Finset.prod_pos fun u _ => hσ u)
        (baseMass N p))
      (uniformBaseResidueLaw (∏ u, σ u) d) ≤ epsilonBase N
  row_integer_on_support : ∀ N p x, goodDomain N p → baseMass N p x ≠ 0 →
    ∀ u, (linearRowValue rowCoeff N p u x).den = 1
  row_denominators_are_units : ∀ N p, goodDomain N p → ∀ r (_hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u j,
      Nat.Coprime (rowCoeff N p u j).den r
  row_primitive : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N → ∀ u, ∃ j,
      rationalResidue r hr (rowCoeff N p u j) ≠ 0
  pairwise_row_tests : ∀ N p, goodDomain N p → ∀ r (hr : r.Prime),
    N + 1 < r → r ≤ V N →
      (∀ Q ∈ tests, ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
      ∀ u v, u ≠ v → ∃ i j,
        rationalResidue r hr (rowCoeff N p u i) *
            rationalResidue r hr (rowCoeff N p v j) ≠
          rationalResidue r hr (rowCoeff N p u j) *
            rationalResidue r hr (rowCoeff N p v i)
  crt_error_bound : ∀ N,
    finiteL1
      (primeTupleCRTLaw
        (fun i => (S.primeStage.pool N (gap i)).lower)
        (fun i => (S.primeStage.pool N (gap i)).upper) (N + 1) (V N))
      (uniformPrimeTupleCRTLaw (N + 1) (V N)) ≤ epsilonCRT N
  epsilonBase_superpolynomial : SuperPolynomialSmall epsilonBase (fun N => (V N : ℝ))
  epsilonCRT_superpolynomial : SuperPolynomialSmall epsilonCRT (fun N => (V N : ℝ))

/-- `O(V^q)`-bounded divisor-weight product average over a prime-only event. -/
def weightedLinearFormsAverage {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) : ℝ :=
  ∑' p : Fin m → ℕ,
    independentPrimePoolMass
      (fun i => (S.primeStage.pool N (D.gap i)).lower)
      (fun i => (S.primeStage.pool N (D.gap i)).upper) p *
      (if E p then 1 else 0) *
      (∑' x : Fin d → ℤ,
        D.baseMass N p x *
          ∏ u, nuB
            (divisorTemplateLaw S.core.parameters N (D.divisor u))
            (linearRowValue D.rowCoeff N p u x).num)

/-- Probability of a prime-only event under the independent harmonic pool slots. -/
def weightedLinearFormsEventProbability {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) : ℝ :=
  independentPrimePoolProbability
    (fun i => (S.primeStage.pool N (D.gap i)).lower)
    (fun i => (S.primeStage.pool N (D.gap i)).upper) E

private theorem rowCoefficient_den_coprime_divisorProduct
    {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (slots : Fin m → ℕ) (σ : Fin q → ℕ)
    (hgood : D.goodDomain N slots)
    (hσpos : ∀ u, 1 ≤ σ u) (hσbound : ∀ u, σ u ≤ D.V N)
    (hσcop : ∀ u, Nat.Coprime (σ u) (primorial (N + 1))) :
    ∀ u j, Nat.Coprime (D.rowCoeff N slots u j).den (∏ v, σ v) := by
  classical
  have hdenSigma (u : Fin q) (j : Fin d) (v : Fin q) :
      Nat.Coprime (D.rowCoeff N slots u j).den (σ v) := by
    by_contra hnot
    obtain ⟨r, hr, hrden, hrsigma⟩ :=
      (Nat.Prime.not_coprime_iff_dvd).mp hnot
    have hcopW : Nat.Coprime r (primorial (N + 1)) :=
      (hσcop v).coprime_dvd_left hrsigma
    have hrNotW : ¬ r ∣ primorial (N + 1) := hr.coprime_iff_not_dvd.mp hcopW
    have hrough : N + 1 < r := by
      by_contra hn
      have hrle : r ≤ N + 1 := by omega
      exact hrNotW (hr.dvd_primorial_iff.mpr hrle)
    have hrleV : r ≤ D.V N := by
      apply le_trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (hσpos v)) hrsigma)
      exact hσbound v
    have hunit := D.row_denominators_are_units N slots hgood r hr hrough hrleV u j
    exact (hr.coprime_iff_not_dvd.mp hunit.symm) hrden
  intro u j
  exact Nat.coprime_fintype_prod_right_iff.mpr (fun v => hdenSigma u j v)

private theorem localPowerRows_fromData {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (slots : Fin m → ℕ) (r A : ℕ) (hr : r.Prime)
    (hgood : D.goodDomain N slots) (hrough : N + 1 < r) (hrV : r ≤ D.V N)
    (hA : 0 < A)
    (hregular : ∀ Q ∈ tests,
      ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (slots i : ℤ)))) :
    ∃ coeff : Fin q → Fin d → ZMod (r ^ A),
      (∀ u, ∃ j, IsUnit (coeff u j)) ∧
      (∀ u v, u ≠ v → ∃ i j,
        IsUnit (coeff u i * coeff v j - coeff u j * coeff v i)) := by
  classical
  let rows : Fin q → Fin d → ℚ := fun u j => D.rowCoeff N slots u j
  have hden (u : Fin q) (j : Fin d) : Nat.Coprime (rows u j).den r := by
    exact D.row_denominators_are_units N slots hgood r hr hrough hrV u j
  let coeff : Fin q → Fin d → ZMod (r ^ A) :=
    rationalRowsModPow (p := r) (A := A) rows hden
  refine ⟨coeff, ?_, ?_⟩
  · intro u
    apply rationalRowsModPow_row_unit hr hA rows hden u
    simpa [rows] using D.row_primitive N slots hgood r hr hrough hrV u
  · intro u v huv
    obtain ⟨i, j, hminor⟩ := D.pairwise_row_tests N slots hgood r hr hrough hrV
      hregular u v huv
    exact ⟨i, j, rationalRowsModPow_minor_unit hr hA rows hden u v i j
      (by simpa [rows] using hminor)⟩

private theorem localClearedRows_fromData {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (slots : Fin m → ℕ) (p A : ℕ) (hp : p.Prime)
    (hgood : D.goodDomain N slots) (hrough : N + 1 < p) (hpV : p ≤ D.V N)
    (hA : 0 < A) :
    ∃ coeff : Fin q → Fin d → ZMod (p ^ A),
      (∀ u, ∃ j, IsUnit (coeff u j)) ∧
      (∀ u v, u ≠ v →
        (∀ Q ∈ tests,
          ¬ ((p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (slots i : ℤ)))) →
        ∃ i j, IsUnit (coeff u i * coeff v j - coeff u j * coeff v i)) ∧
      (∀ u j, coeff u j =
        (rationalRowDenominator (fun i => D.rowCoeff N slots u i) : ZMod (p ^ A)) *
          rationalRowsModPow (p := p) (A := A)
            (fun v i => D.rowCoeff N slots v i)
            (fun v i => D.row_denominators_are_units N slots hgood p hp hrough hpV v i)
            u j) := by
  classical
  let rows : Fin q → Fin d → ℚ := fun u j => D.rowCoeff N slots u j
  have hdenP (u : Fin q) (j : Fin d) : Nat.Coprime (rows u j).den p := by
    exact D.row_denominators_are_units N slots hgood p hp hrough hpV u j
  have hdenPow (u : Fin q) (j : Fin d) : Nat.Coprime (rows u j).den (p ^ A) := by
    by_cases hA : A = 0
    · simp [hA]
    · rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hA)]
      exact hdenP u j
  let ratCoeff : Fin q → Fin d → ZMod (p ^ A) :=
    rationalRowsModPow (p := p) (A := A) rows hdenP
  let clearedCoeff : Fin q → Fin d → ZMod (p ^ A) := fun u j =>
    (rationalRowClearedCoefficient (rows u) j : ZMod (p ^ A))
  have hDdenUnit (u : Fin q) :
      IsUnit (rationalRowDenominator (rows u) : ZMod (p ^ A)) := by
    apply (ZMod.isUnit_iff_coprime _ _).2
    dsimp [rationalRowDenominator]
    exact Nat.coprime_fintype_prod_left_iff.mpr (hdenPow u)
  have hclear (u : Fin q) (j : Fin d) :
      rationalRowDenominator (rows u) * ratCoeff u j = clearedCoeff u j := by
    have h := rationalRow_clearedCoefficient_modulus (rows u) (hdenPow u) j
    simpa [ratCoeff, clearedCoeff, rationalRowsModPow,
      rationalResidueModPow, rationalResidueModulus] using h
  have hprimitive (u : Fin q) : ∃ j, IsUnit (ratCoeff u j) := by
    apply rationalRowsModPow_row_unit hp hA rows hdenP u
    simpa [rows] using D.row_primitive N slots hgood p hp hrough hpV u
  refine ⟨clearedCoeff, ?_, ?_, ?_⟩
  · intro u
    obtain ⟨j, hj⟩ := hprimitive u
    refine ⟨j, ?_⟩
    rw [← hclear u j]
    exact IsUnit.mul (hDdenUnit u) hj
  · intro u v huv
    intro hregular
    obtain ⟨i, j, hminor⟩ := D.pairwise_row_tests N slots hgood p hp hrough hpV
      hregular u v huv
    have hminorRat := rationalRowsModPow_minor_unit hp hA rows hdenP u v i j
      (by simpa [rows] using hminor)
    refine ⟨i, j, ?_⟩
    have hdet : clearedCoeff u i * clearedCoeff v j -
        clearedCoeff u j * clearedCoeff v i =
          (rationalRowDenominator (rows u) : ZMod (p ^ A)) *
            (rationalRowDenominator (rows v) : ZMod (p ^ A)) *
              (ratCoeff u i * ratCoeff v j - ratCoeff u j * ratCoeff v i) := by
      rw [← hclear u i, ← hclear v j, ← hclear u j, ← hclear v i]
      ring
    rw [hdet]
    exact IsUnit.mul (IsUnit.mul (hDdenUnit u) (hDdenUnit v)) hminorRat
  · intro u j
    simpa [clearedCoeff, ratCoeff] using (hclear u j).symm

/-- Kernel probability of a homomorphism between finite groups, under uniform input. -/
def localKernelProbability {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) : ℝ :=
  (Fintype.card f.ker : ℝ) / Fintype.card G

/-- Normalized divisibility kernel count `|H|·P(f(x)=1)`, the local factor αₚ. -/
def normalizedKernelCount {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) : ℝ :=
  (Fintype.card H : ℝ) * localKernelProbability f

/-- A homomorphism's kernel and image cardinalities multiply to the domain size. -/
theorem finite_group_kernel_cardinality {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) :
    Fintype.card G = Fintype.card f.ker * Fintype.card f.range := by
  rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  simp only [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The normalized local divisibility count is at least one; if the local map is surjective,
it is exactly one. These are the homomorphism steps used in the local kernel calculation. -/
theorem local_linear_kernel_count_excess {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) :
    1 ≤ normalizedKernelCount f ∧ (Function.Surjective f → normalizedKernelCount f = 1) := by
  have hcard := finite_group_kernel_cardinality f
  have hcardR : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ) := by
    exact_mod_cast hcard
  have hK : (0 : ℝ) < (Fintype.card f.ker : ℝ) := by positivity
  have hR : (0 : ℝ) < (Fintype.card f.range : ℝ) := by positivity
  have hle : Fintype.card f.range ≤ Fintype.card H :=
    Fintype.card_le_of_injective (fun x : f.range => (x : H)) Subtype.val_injective
  have hleR : (Fintype.card f.range : ℝ) ≤ (Fintype.card H : ℝ) := by
    exact_mod_cast hle
  constructor
  · change 1 ≤ (Fintype.card H : ℝ) *
      ((Fintype.card f.ker : ℝ) / (Fintype.card G : ℝ))
    rw [hcardR]
    have hfrac : (Fintype.card H : ℝ) *
        ((Fintype.card f.ker : ℝ) /
          ((Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ))) =
        (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
      field_simp
    rw [hfrac]
    exact (one_le_div hR).2 hleR
  · intro hsurj
    have hbij : Function.Bijective (fun x : f.range => (x : H)) :=
      ⟨Subtype.val_injective, fun y => ⟨⟨y, hsurj y⟩, rfl⟩⟩
    have hR_eq : (Fintype.card f.range : ℝ) = (Fintype.card H : ℝ) := by
      exact_mod_cast Fintype.card_congr (Equiv.ofBijective _ hbij)
    change (Fintype.card H : ℝ) *
      ((Fintype.card f.ker : ℝ) / (Fintype.card G : ℝ)) = 1
    rw [hcardR]
    have hfrac : (Fintype.card H : ℝ) *
        ((Fintype.card f.ker : ℝ) /
          ((Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ))) =
        (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
      field_simp
    rw [hfrac, hR_eq]
    field_simp

private theorem normalizedKernelCount_le_of_surjective_projection
    {G H H₁ : Type*} [Group G] [Group H] [Group H₁]
    [Fintype G] [Fintype H] [Fintype H₁]
    (f : G →* H) (π : H →* H₁)
    (hsurj : Function.Surjective (π.comp f)) :
    normalizedKernelCount f ≤ (Fintype.card H : ℝ) / Fintype.card H₁ := by
  have hcard := finite_group_kernel_cardinality f
  have hcardR : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ) := by
    exact_mod_cast hcard
  let proj : f.range →* H₁ := π.comp f.range.subtype
  have hproj : Function.Surjective proj := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨⟨f x, ⟨x, rfl⟩⟩, ?_⟩
    exact hx
  have hcardRange : Fintype.card H₁ ≤ Fintype.card f.range :=
    Fintype.card_le_of_surjective proj hproj
  have hcardRangeR : (Fintype.card H₁ : ℝ) ≤ (Fintype.card f.range : ℝ) := by
    exact_mod_cast hcardRange
  have hrangePos : (0 : ℝ) < (Fintype.card f.range : ℝ) := by positivity
  have htargetPos : (0 : ℝ) < (Fintype.card H₁ : ℝ) := by positivity
  have hkernelPos : (0 : ℝ) < (Fintype.card f.ker : ℝ) := by positivity
  have hnormal : normalizedKernelCount f =
      (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
    calc
      normalizedKernelCount f = (Fintype.card H : ℝ) *
          ((Fintype.card f.ker : ℝ) / (Fintype.card G : ℝ)) := rfl
      _ = (Fintype.card H : ℝ) *
          ((Fintype.card f.ker : ℝ) /
            ((Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ))) := by
          rw [hcardR]
      _ = (Fintype.card H : ℝ) / (Fintype.card f.range : ℝ) := by
          field_simp
  calc
    normalizedKernelCount f = (Fintype.card H : ℝ) /
        (Fintype.card f.range : ℝ) := hnormal
    _ = (Fintype.card H : ℝ) * (1 / (Fintype.card f.range : ℝ)) := by ring
    _ ≤ (Fintype.card H : ℝ) * (1 / (Fintype.card H₁ : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact one_div_le_one_div_of_le htargetPos hcardRangeR
    _ = (Fintype.card H : ℝ) / Fintype.card H₁ := by ring

private def localPrimePowerCast {p A a : ℕ} (ha : a ≤ A) :
    ZMod (p ^ A) →+* ZMod (p ^ a) :=
  ZMod.castHom (m := p ^ a) (n := p ^ A) (Nat.pow_dvd_pow p ha) (ZMod (p ^ a))

private def localRowModulusValue {p A q d : ℕ}
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (u : Fin q) (x : Fin d → ZMod (p ^ A)) : ZMod (p ^ (a u)) :=
  localPrimePowerCast (ha u) (∑ j, coeff u j * x j)

private def localDivisibilityAddHom {p A q d : ℕ}
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A)) :
    (Fin d → ZMod (p ^ A)) →+ ((u : Fin q) → ZMod (p ^ (a u))) where
  toFun := fun x u => localRowModulusValue a ha coeff u x
  map_zero' := by
    funext u
    simp [localRowModulusValue, localPrimePowerCast]
  map_add' := by
    intro x y
    funext u
    have hsum :
        (∑ j, coeff u j * (x j + y j)) =
          (∑ j, coeff u j * x j) + (∑ j, coeff u j * y j) := by
      calc
        (∑ j, coeff u j * (x j + y j)) =
            ∑ j, (coeff u j * x j + coeff u j * y j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := Finset.sum_add_distrib
    change localPrimePowerCast (ha u) (∑ j, coeff u j * (x j + y j)) =
      localPrimePowerCast (ha u) (∑ j, coeff u j * x j) +
        localPrimePowerCast (ha u) (∑ j, coeff u j * y j)
    rw [hsum]
    exact map_add (localPrimePowerCast (ha u)) _ _

private def globalRowModulusValue {K q d : ℕ}
    (σ : Fin q → ℕ) (hdiv : ∀ u, σ u ∣ K)
    (coeff : Fin q → Fin d → ZMod K)
    (u : Fin q) (x : Fin d → ZMod K) : ZMod (σ u) :=
  ZMod.castHom (hdiv u) (ZMod (σ u)) (∑ j, coeff u j * x j)

private def globalDivisibilityAddHom {K q d : ℕ}
    (σ : Fin q → ℕ) (hdiv : ∀ u, σ u ∣ K)
    (coeff : Fin q → Fin d → ZMod K) :
    (Fin d → ZMod K) →+ ((u : Fin q) → ZMod (σ u)) where
  toFun := fun x u => globalRowModulusValue σ hdiv coeff u x
  map_zero' := by
    funext u
    simp [globalRowModulusValue]
  map_add' := by
    intro x y
    funext u
    have hsum :
        (∑ j, coeff u j * (x j + y j)) =
          (∑ j, coeff u j * x j) + (∑ j, coeff u j * y j) := by
      calc
        (∑ j, coeff u j * (x j + y j)) =
            ∑ j, (coeff u j * x j + coeff u j * y j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := Finset.sum_add_distrib
    change ZMod.castHom (hdiv u) (ZMod (σ u))
        (∑ j, coeff u j * (x j + y j)) =
      ZMod.castHom (hdiv u) (ZMod (σ u)) (∑ j, coeff u j * x j) +
        ZMod.castHom (hdiv u) (ZMod (σ u)) (∑ j, coeff u j * y j)
    rw [hsum]
    exact map_add (ZMod.castHom (hdiv u) (ZMod (σ u))) _ _

private theorem globalDivisibility_crt_factor {K q d : ℕ}
    (σ : Fin q → ℕ) (hσ : ∀ u, σ u ≠ 0) (hK : K ≠ 0)
    (hdiv : ∀ u, σ u ∣ K) (coeff : Fin q → Fin d → ZMod K)
    (x : Fin d → ZMod K) :
    rowPrimePowerCRTVectorEquiv σ hσ hK hdiv
        (globalDivisibilityAddHom σ hdiv coeff x) =
      fun p => localDivisibilityAddHom
        (fun u => (σ u).factorization p.val)
        (fun u => ((Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)) p.val)
        (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p)
        ((primePowerCRTVectorEquiv K d hK x) p) := by
  classical
  have hfac (u : Fin q) : (σ u).factorization ≤ K.factorization :=
    (Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)
  ext p u
  let A : ℕ := K.factorization p.val
  let a : Fin q → ℕ := fun u => (σ u).factorization p.val
  have ha (u : Fin q) : a u ≤ A := hfac u p.val
  let cP : Fin q → Fin d → ZMod (p.val ^ A) := fun u j =>
    (primePowerCRTRingEquiv K hK (coeff u j)) p
  let xP : Fin d → ZMod (p.val ^ A) :=
    fun j => (primePowerCRTVectorEquiv K d hK x) p j
  have hpowK : p.val ^ A ∣ K := by
    change p.val ^ K.factorization p.val ∣ K
    exact (primePowerIndex_prime p).pow_dvd_iff_le_factorization hK |>.2 le_rfl
  have hpowMid (u : Fin q) : p.val ^ (a u) ∣ p.val ^ A :=
    Nat.pow_dvd_pow p.val (ha u)
  have hpowRow (u : Fin q) : p.val ^ (a u) ∣ σ u := by
    change p.val ^ (σ u).factorization p.val ∣ σ u
    exact (primePowerIndex_prime p).pow_dvd_iff_le_factorization (hσ u) |>.2 le_rfl
  let f (u : Fin q) : ZMod K →+* ZMod (p.val ^ (a u)) :=
    ZMod.castHom (dvd_trans (hpowMid u) hpowK) (ZMod (p.val ^ (a u)))
  have hbaseCoeff (u : Fin q) (j : Fin d) :
      cP u j = ZMod.castHom hpowK (ZMod (p.val ^ A)) (coeff u j) := by
    change (primePowerCRTRingEquiv K hK (coeff u j)) p = _
    exact primePowerCRTRingEquiv_apply hK (coeff u j) p
  have hbaseX (j : Fin d) :
      xP j = ZMod.castHom hpowK (ZMod (p.val ^ A)) (x j) := by
    change (primePowerCRTRingEquiv K hK (x j)) p = _
    exact primePowerCRTRingEquiv_apply hK (x j) p
  have hcoefCast (u : Fin q) (j : Fin d) :
      localPrimePowerCast (ha u) (cP u j) = f u (coeff u j) := by
    calc
      localPrimePowerCast (ha u) (cP u j) =
          ZMod.castHom (hpowMid u) (ZMod (p.val ^ (a u)))
            (ZMod.castHom hpowK (ZMod (p.val ^ A)) (coeff u j)) := by
              rw [hbaseCoeff]
              rfl
      _ = f u (coeff u j) := by
        change ((ZMod.castHom (hpowMid u) (ZMod (p.val ^ (a u)))).comp
          (ZMod.castHom hpowK (ZMod (p.val ^ A)))) (coeff u j) = _
        rw [ZMod.castHom_comp]
  have hxCast (u : Fin q) (j : Fin d) :
      localPrimePowerCast (ha u) (xP j) = f u (x j) := by
    calc
      localPrimePowerCast (ha u) (xP j) =
          ZMod.castHom (hpowMid u) (ZMod (p.val ^ (a u)))
            (ZMod.castHom hpowK (ZMod (p.val ^ A)) (x j)) := by
              rw [hbaseX]
              rfl
      _ = f u (x j) := by
        change ((ZMod.castHom (hpowMid u) (ZMod (p.val ^ (a u)))).comp
          (ZMod.castHom hpowK (ZMod (p.val ^ A)))) (x j) = _
        rw [ZMod.castHom_comp]
  have hlocal (u : Fin q) :
      localRowModulusValue a ha cP u (xP) =
        f u (∑ j, coeff u j * x j) := by
    change localPrimePowerCast (ha u) (∑ j, cP u j * xP j) = _
    calc
      _ = ∑ j, localPrimePowerCast (ha u) (cP u j * xP j) := by rw [map_sum]
      _ = ∑ j, f u (coeff u j) * f u (x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul, hcoefCast, hxCast]
      _ = f u (∑ j, coeff u j * x j) := by
        calc
          (∑ j, f u (coeff u j) * f u (x j)) =
              ∑ j, f u (coeff u j * x j) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [map_mul]
          _ = f u (∑ j, coeff u j * x j) :=
            (map_sum (f u) (fun j : Fin d => coeff u j * x j) Finset.univ).symm
  have hglobal (u : Fin q) :
      (rowPrimePowerCRTRingEquiv (hσ u) hK (hdiv u)
        (globalRowModulusValue σ hdiv coeff u x)) p =
        f u (∑ j, coeff u j * x j) := by
    rw [rowPrimePowerCRTRingEquiv_apply]
    change ((ZMod.castHom (hpowRow u) (ZMod (p.val ^ (a u)))).comp
      (ZMod.castHom (hdiv u) (ZMod (σ u)))) (∑ j, coeff u j * x j) = _
    rw [ZMod.castHom_comp]
  change (rowPrimePowerCRTRingEquiv (hσ u) hK (hdiv u)
      (globalRowModulusValue σ hdiv coeff u x)) p =
    localRowModulusValue a ha cP u xP
  exact (hglobal u).trans (hlocal u).symm

private def localDivisibilityGroupHom {p A q d : ℕ}
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A)) :
    Multiplicative (Fin d → ZMod (p ^ A)) →*
      Multiplicative ((u : Fin q) → ZMod (p ^ (a u))) :=
  (localDivisibilityAddHom a ha coeff).toMultiplicative

private def localDivisibilityProductAddHom {P : Type*} {q d : ℕ}
    (prime : P → ℕ) (A : P → ℕ) (a : (p : P) → Fin q → ℕ)
    (ha : ∀ p u, a p u ≤ A p)
    (coeff : ∀ p, Fin q → Fin d → ZMod (prime p ^ A p)) :
    ((p : P) → Fin d → ZMod (prime p ^ A p)) →+
      ((p : P) → (u : Fin q) → ZMod (prime p ^ (a p u))) where
  toFun := fun x p => localDivisibilityAddHom (a p) (ha p) (coeff p) (x p)
  map_zero' := by
    funext p u
    exact congrFun (localDivisibilityAddHom (a p) (ha p) (coeff p)).map_zero u
  map_add' := by
    intro x y
    funext p u
    exact congrFun
      ((localDivisibilityAddHom (a p) (ha p) (coeff p)).map_add (x p) (y p)) u

private def localDivisibilityProductGroupHom {P : Type*} {q d : ℕ}
    (prime : P → ℕ) (A : P → ℕ) (a : (p : P) → Fin q → ℕ)
    (ha : ∀ p u, a p u ≤ A p)
    (coeff : ∀ p, Fin q → Fin d → ZMod (prime p ^ A p)) :
    Multiplicative ((p : P) → Fin d → ZMod (prime p ^ A p)) →*
      Multiplicative ((p : P) → (u : Fin q) → ZMod (prime p ^ (a p u))) :=
  (localDivisibilityProductAddHom prime A a ha coeff).toMultiplicative

private def piGroupHom {ι : Type*}
    (G H : ι → Type*) [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) : (∀ i, G i) →* (∀ i, H i) where
  toFun := fun x i => f i (x i)
  map_one' := by ext i; simp
  map_mul' := by intro x y; ext i; simp

private def multiplicativePiEquiv {ι : Type*} (G : ι → Type*)
    [∀ i, AddGroup (G i)] :
    Multiplicative ((i : ι) → G i) ≃* ((i : ι) → Multiplicative (G i)) where
  toFun := fun x i => Multiplicative.ofAdd (x.toAdd i)
  invFun := fun x => Multiplicative.ofAdd (fun i => (x i).toAdd)
  left_inv := by intro x; rfl
  right_inv := by intro x; funext i; rfl
  map_mul' := by intro x y; ext i; rfl

private theorem normalizedKernelCount_piHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : ι → Type*) [∀ i, Group (G i)] [∀ i, Group (H i)]
    [∀ i, Fintype (G i)] [∀ i, Fintype (H i)]
    (f : ∀ i, G i →* H i) :
    normalizedKernelCount (piGroupHom G H f) =
      ∏ i, normalizedKernelCount (f i) := by
  let eFun : (piGroupHom G H f).ker → (∀ i, (f i).ker) := fun x i =>
    (⟨x.val i, by
      have hx := congrFun x.property i
      simpa [piGroupHom] using hx⟩ : (f i).ker)
  let eInv : (∀ i, (f i).ker) → (piGroupHom G H f).ker := fun x =>
    (⟨fun i => (x i).val, by
      ext i
      exact (x i).property⟩ : (piGroupHom G H f).ker)
  have eleft : ∀ x, eInv (eFun x) = x := by
    intro x
    apply Subtype.ext
    funext i
    rfl
  have eright : ∀ x, eFun (eInv x) = x := by
    intro x
    funext i
    apply Subtype.ext
    rfl
  let hkerEquiv : (piGroupHom G H f).ker ≃ (∀ i, (f i).ker) :=
    ⟨eFun, eInv, eleft, eright⟩
  have hcardG : Nat.card (∀ i, G i) = ∏ i, Nat.card (G i) := Nat.card_pi
  have hcardH : Nat.card (∀ i, H i) = ∏ i, Nat.card (H i) := Nat.card_pi
  have hcardKer : Nat.card (piGroupHom G H f).ker = ∏ i, Nat.card (f i).ker := by
    calc
      _ = Nat.card (∀ i, (f i).ker) := Nat.card_congr hkerEquiv
      _ = _ := Nat.card_pi
  have hcardGReal : (Nat.card (∀ i, G i) : ℝ) = ∏ i, (Nat.card (G i) : ℝ) := by
    exact_mod_cast hcardG
  have hcardHReal : (Nat.card (∀ i, H i) : ℝ) = ∏ i, (Nat.card (H i) : ℝ) := by
    exact_mod_cast hcardH
  have hcardKerReal :
      (Nat.card (piGroupHom G H f).ker : ℝ) = ∏ i, (Nat.card (f i).ker : ℝ) := by
    exact_mod_cast hcardKer
  unfold normalizedKernelCount localKernelProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [hcardHReal, hcardKerReal, hcardGReal]
  calc
    (∏ i, (Nat.card (H i) : ℝ)) *
        ((∏ i, (Nat.card (f i).ker : ℝ)) /
          ∏ i, (Nat.card (G i) : ℝ)) =
      (∏ i, (Nat.card (H i) : ℝ)) *
        ∏ i, ((Nat.card (f i).ker : ℝ) / Nat.card (G i)) := by
          rw [Finset.prod_div_distrib]
    _ = ∏ i, ((Nat.card (H i) : ℝ) *
        ((Nat.card (f i).ker : ℝ) / Nat.card (G i))) :=
      (Finset.prod_mul_distrib).symm

private theorem normalizedKernelCount_congr_of_commuting
    {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
    [Fintype G] [Fintype H] [Fintype G'] [Fintype H']
    (f : G →* H) (g : G' →* H') (eG : G ≃* G') (eH : H ≃* H')
    (hcomm : ∀ x, eH (f x) = g (eG x)) :
    normalizedKernelCount f = normalizedKernelCount g := by
  classical
  let eKer : f.ker ≃ g.ker := {
    toFun := fun x => ⟨eG x.val, by
      have hx := hcomm x.val
      rw [x.property, map_one] at hx
      exact hx.symm⟩
    invFun := fun y => ⟨eG.symm y.val, by
      apply eH.injective
      calc
        eH (f (eG.symm y.val)) = g (eG (eG.symm y.val)) := hcomm _
        _ = g y.val := by simp
        _ = 1 := y.property
        _ = eH 1 := by simp
    ⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro y; apply Subtype.ext; simp
  }
  have hG : Fintype.card G = Fintype.card G' := Fintype.card_congr eG.toEquiv
  have hH : Fintype.card H = Fintype.card H' := Fintype.card_congr eH.toEquiv
  have hK : Fintype.card f.ker = Fintype.card g.ker := Fintype.card_congr eKer
  unfold normalizedKernelCount localKernelProbability
  rw [hH, hK, hG]

private theorem globalDivisibility_normalizedKernelCount_factor {K q d : ℕ}
    (σ : Fin q → ℕ) (hσ : ∀ u, σ u ≠ 0) (hK : K ≠ 0)
    (hdiv : ∀ u, σ u ∣ K) (coeff : Fin q → Fin d → ZMod K)
    [DecidableEq (primePowerIndex K)] [Fintype (primePowerIndex K)]
    [Fintype (Multiplicative (Fin d → ZMod K))]
    [Fintype (Multiplicative ((u : Fin q) → ZMod (σ u)))]
    [∀ p : primePowerIndex K,
      Fintype (Multiplicative (Fin d → ZMod (p.val ^ K.factorization p.val)))]
    [∀ p : primePowerIndex K,
      Fintype (Multiplicative ((u : Fin q) →
        ZMod (p.val ^ (σ u).factorization p.val)))] :
    normalizedKernelCount ((globalDivisibilityAddHom σ hdiv coeff).toMultiplicative) =
      ∏ p : primePowerIndex K,
        normalizedKernelCount (localDivisibilityGroupHom
          (fun u => (σ u).factorization p.val)
          (fun u => (Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u) p.val)
          (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p)) := by
  classical
  have hfac (u : Fin q) : (σ u).factorization ≤ K.factorization :=
    (Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)
  let A : primePowerIndex K → ℕ := fun p => K.factorization p.val
  let a : (p : primePowerIndex K) → Fin q → ℕ := fun p u =>
    (σ u).factorization p.val
  have ha (p : primePowerIndex K) (u : Fin q) : a p u ≤ A p := hfac u p.val
  let cP : (p : primePowerIndex K) → Fin q → Fin d → ZMod (p.val ^ A p) :=
    fun p u j => (primePowerCRTRingEquiv K hK (coeff u j)) p
  let globalF : Multiplicative (Fin d → ZMod K) →*
      Multiplicative ((u : Fin q) → ZMod (σ u)) :=
    (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative
  let localG : primePowerIndex K → Type := fun p =>
    Multiplicative (Fin d → ZMod (p.val ^ A p))
  let localH : primePowerIndex K → Type := fun p =>
    Multiplicative ((u : Fin q) → ZMod (p.val ^ (a p u)))
  let localHom : (p : primePowerIndex K) → localG p →* localH p := fun p =>
    localDivisibilityGroupHom (a p) (ha p) (cP p)
  let localPiHom := piGroupHom localG localH localHom
  let baseCRT : (Fin d → ZMod K) ≃+*
      ((p : primePowerIndex K) → Fin d → ZMod (p.val ^ A p)) :=
    primePowerCRTVectorEquiv K d hK
  let rowCRT : ((u : Fin q) → ZMod (σ u)) ≃+*
      ((p : primePowerIndex K) → (u : Fin q) →
        ZMod (p.val ^ (a p u))) :=
    rowPrimePowerCRTVectorEquiv σ hσ hK hdiv
  let eG : Multiplicative (Fin d → ZMod K) ≃*
      ((p : primePowerIndex K) → localG p) :=
    baseCRT.toAddEquiv.toMultiplicative.trans
      (multiplicativePiEquiv (fun p => Fin d → ZMod (p.val ^ A p)))
  let eH : Multiplicative ((u : Fin q) → ZMod (σ u)) ≃*
      ((p : primePowerIndex K) → localH p) :=
    rowCRT.toAddEquiv.toMultiplicative.trans
      (multiplicativePiEquiv (fun p => (u : Fin q) → ZMod (p.val ^ (a p u))))
  have hcomm : ∀ x, eH (globalF x) = localPiHom (eG x) := by
    intro x
    ext p u
    have hcrt := globalDivisibility_crt_factor σ hσ hK hdiv coeff x.toAdd
    change Multiplicative.ofAdd
        (rowPrimePowerCRTVectorEquiv σ hσ hK hdiv
          (globalDivisibilityAddHom σ hdiv coeff x.toAdd) p u) =
      Multiplicative.ofAdd
        (localDivisibilityAddHom (a p) (ha p) (cP p)
          (baseCRT x.toAdd p) u)
    exact congrArg Multiplicative.ofAdd (congrFun (congrFun hcrt p) u)
  have hconj := normalizedKernelCount_congr_of_commuting globalF localPiHom eG eH hcomm
  calc
    normalizedKernelCount globalF = normalizedKernelCount localPiHom := hconj
    _ = ∏ p, normalizedKernelCount (localHom p) :=
      normalizedKernelCount_piHom localG localH localHom

private def localCoordinateProjection {p q : ℕ} (a : Fin q → ℕ) (u : Fin q) :
    Multiplicative ((v : Fin q) → ZMod (p ^ (a v))) →*
      Multiplicative (ZMod (p ^ (a u))) where
  toFun := fun y => Multiplicative.ofAdd (y.toAdd u)
  map_one' := rfl
  map_mul' := by intro x y; rfl

private def localTwoCoordinateProjection {p q : ℕ} (a : Fin q → ℕ)
    (u v : Fin q) :
    Multiplicative ((i : Fin q) → ZMod (p ^ (a i))) →*
      Multiplicative (ZMod (p ^ (a u)) × ZMod (p ^ (a v))) where
  toFun := fun y => Multiplicative.ofAdd (y.toAdd u, y.toAdd v)
  map_one' := rfl
  map_mul' := by intro x y; rfl

private theorem localCoordinate_projection_surjective {p A q d : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A)) (u : Fin q)
    (hrow : ∃ j, IsUnit (coeff u j)) :
    Function.Surjective
      ((localCoordinateProjection a u).comp (localDivisibilityGroupHom a ha coeff)) := by
  classical
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI : NeZero (p ^ (a u)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  intro y
  obtain ⟨j, hj⟩ := hrow
  let yLift : ZMod (p ^ A) := (y.toAdd.val : ZMod (p ^ A))
  have hlift : localPrimePowerCast (ha u) yLift = y.toAdd := by
    change (ZMod.castHom (m := p ^ (a u)) (n := p ^ A) (Nat.pow_dvd_pow p (ha u))
      (ZMod (p ^ (a u)))) (y.toAdd.val : ZMod (p ^ A)) = y.toAdd
    simp [yLift, ZMod.castHom_apply, ZMod.natCast_zmod_val]
  let x : Fin d → ZMod (p ^ A) := fun k =>
    if k = j then yLift * ↑(hj.unit⁻¹) else 0
  have hunitInv : coeff u j * ↑(hj.unit⁻¹) = 1 := by
    calc
      coeff u j * ↑(hj.unit⁻¹) = (↑hj.unit : ZMod (p ^ A)) * ↑(hj.unit⁻¹) := by
        rw [hj.unit_spec]
      _ = 1 := by simpa using Units.val_inv hj.unit
  have hsum :
      (∑ k, coeff u k * x k) = coeff u j * (yLift * ↑(hj.unit⁻¹)) := by
    dsimp [x]
    simp [Finset.sum_ite_eq', eq_comm]
  have hrowValue : (∑ k, coeff u k * x k) = yLift := by
    calc
      _ = coeff u j * (yLift * ↑(hj.unit⁻¹)) := hsum
      _ = yLift * (coeff u j * ↑(hj.unit⁻¹)) := by ring
      _ = yLift := by rw [hunitInv, mul_one]
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  change Multiplicative.ofAdd (localRowModulusValue a ha coeff u x) =
    Multiplicative.ofAdd y.toAdd
  congr 1
  calc
    localRowModulusValue a ha coeff u x =
        localPrimePowerCast (ha u) (∑ k, coeff u k * x k) := rfl
    _ = localPrimePowerCast (ha u) yLift := by rw [hrowValue]
    _ = y.toAdd := hlift

private theorem localTwoCoordinate_projection_surjective {p A q d : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (u v : Fin q) (i j : Fin d) (hij : i ≠ j)
    (hdet : IsUnit (coeff u i * coeff v j - coeff u j * coeff v i)) :
    Function.Surjective
      ((localTwoCoordinateProjection a u v).comp
        (localDivisibilityGroupHom a ha coeff)) := by
  classical
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI : NeZero (p ^ (a u)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI : NeZero (p ^ (a v)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  intro target
  let y : ZMod (p ^ (a u)) := target.toAdd.1
  let z : ZMod (p ^ (a v)) := target.toAdd.2
  let yLift : ZMod (p ^ A) := (y.val : ZMod (p ^ A))
  let zLift : ZMod (p ^ A) := (z.val : ZMod (p ^ A))
  have hyLift : localPrimePowerCast (ha u) yLift = y := by
    change (ZMod.castHom (m := p ^ (a u)) (n := p ^ A)
      (Nat.pow_dvd_pow p (ha u)) (ZMod (p ^ (a u))))
      (y.val : ZMod (p ^ A)) = y
    simp [yLift, ZMod.castHom_apply, ZMod.natCast_zmod_val]
  have hzLift : localPrimePowerCast (ha v) zLift = z := by
    change (ZMod.castHom (m := p ^ (a v)) (n := p ^ A)
      (Nat.pow_dvd_pow p (ha v)) (ZMod (p ^ (a v))))
      (z.val : ZMod (p ^ A)) = z
    simp [zLift, ZMod.castHom_apply, ZMod.natCast_zmod_val]
  let c11 := coeff u i
  let c12 := coeff u j
  let c21 := coeff v i
  let c22 := coeff v j
  let det : ZMod (p ^ A) := c11 * c22 - c12 * c21
  have hdetInv : (↑(hdet.unit⁻¹) : ZMod (p ^ A)) *
      (coeff u i * coeff v j - coeff u j * coeff v i) = 1 := by
    calc
      _ = (↑(hdet.unit⁻¹) : ZMod (p ^ A)) * ↑hdet.unit :=
        congrArg (fun z => (↑(hdet.unit⁻¹) : ZMod (p ^ A)) * z)
        hdet.unit_spec.symm
      _ = 1 := by simpa using Units.inv_val hdet.unit
  let xi : ZMod (p ^ A) := ↑(hdet.unit⁻¹) * (c22 * yLift - c12 * zLift)
  let xj : ZMod (p ^ A) := ↑(hdet.unit⁻¹) * (c11 * zLift - c21 * yLift)
  let x : Fin d → ZMod (p ^ A) := fun k =>
    (if k = i then xi else 0) + (if k = j then xj else 0)
  have hlinear (w : Fin q) :
      (∑ k, coeff w k * x k) = coeff w i * xi + coeff w j * xj := by
    calc
      (∑ k, coeff w k * x k) =
          ∑ k, (coeff w k * (if k = i then xi else 0) +
            coeff w k * (if k = j then xj else 0)) := by
              apply Finset.sum_congr rfl
              intro k hk
              dsimp [x]
              ring
      _ = coeff w i * xi + coeff w j * xj := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', eq_comm]
  have hrowU : coeff u i * xi + coeff u j * xj = yLift := by
    dsimp [xi, xj, c11, c12, c21, c22, det]
    calc
      _ = ↑(hdet.unit⁻¹) *
          ((coeff u i * coeff v j - coeff u j * coeff v i) * yLift) := by ring
      _ = yLift := by
        calc
          _ = (↑(hdet.unit⁻¹) *
              (coeff u i * coeff v j - coeff u j * coeff v i)) * yLift := by ring
          _ = 1 * yLift := by rw [hdetInv]
          _ = yLift := by ring
  have hrowV : coeff v i * xi + coeff v j * xj = zLift := by
    dsimp [xi, xj, c11, c12, c21, c22, det]
    calc
      _ = ↑(hdet.unit⁻¹) *
          ((coeff u i * coeff v j - coeff u j * coeff v i) * zLift) := by ring
      _ = zLift := by
        calc
          _ = (↑(hdet.unit⁻¹) *
              (coeff u i * coeff v j - coeff u j * coeff v i)) * zLift := by ring
          _ = 1 * zLift := by rw [hdetInv]
          _ = zLift := by ring
  have hvalueU : localRowModulusValue a ha coeff u x = y := by
    calc
      localRowModulusValue a ha coeff u x =
          localPrimePowerCast (ha u) (∑ k, coeff u k * x k) := rfl
      _ = localPrimePowerCast (ha u) yLift := by rw [hlinear u, hrowU]
      _ = y := hyLift
  have hvalueV : localRowModulusValue a ha coeff v x = z := by
    calc
      localRowModulusValue a ha coeff v x =
          localPrimePowerCast (ha v) (∑ k, coeff v k * x k) := rfl
      _ = localPrimePowerCast (ha v) zLift := by rw [hlinear v, hrowV]
      _ = z := hzLift
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  change Multiplicative.ofAdd
      (localRowModulusValue a ha coeff u x, localRowModulusValue a ha coeff v x) =
    Multiplicative.ofAdd (y, z)
  rw [hvalueU, hvalueV]

private theorem localKernel_upper_two_rows {p A q d : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (u v : Fin q) (i j : Fin d) (hij : i ≠ j)
    (hdet : IsUnit (coeff u i * coeff v j - coeff u j * coeff v i))
    [Fintype (Multiplicative (Fin d → ZMod (p ^ A)))]
    [Fintype (Multiplicative ((k : Fin q) → ZMod (p ^ (a k))))]
    [Fintype (Multiplicative
      (ZMod (p ^ (a u)) × ZMod (p ^ (a v))))] :
    normalizedKernelCount (localDivisibilityGroupHom a ha coeff) ≤
      (∏ k, (p : ℝ) ^ (a k)) /
        ((p : ℝ) ^ (a u) * (p : ℝ) ^ (a v)) := by
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI (k : Fin q) : NeZero (p ^ (a k)) :=
    ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  have hsurj := localTwoCoordinate_projection_surjective hp a ha coeff
    u v i j hij hdet
  have hbound := normalizedKernelCount_le_of_surjective_projection
    (localDivisibilityGroupHom a ha coeff) (localTwoCoordinateProjection a u v) hsurj
  have hcardH :
      (Fintype.card (Multiplicative ((k : Fin q) → ZMod (p ^ (a k)))) : ℝ) =
        ∏ k, (p : ℝ) ^ (a k) := by
    calc
      _ = (Fintype.card ((k : Fin q) → ZMod (p ^ (a k))) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = ∏ k, (Fintype.card (ZMod (p ^ (a k))) : ℝ) := by
        exact_mod_cast (Fintype.card_pi :
          Fintype.card ((k : Fin q) → ZMod (p ^ (a k))) =
            ∏ k, Fintype.card (ZMod (p ^ (a k))))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [ZMod.card]
        norm_cast
  have hcardH₁ :
      (Fintype.card
        (Multiplicative (ZMod (p ^ (a u)) × ZMod (p ^ (a v)))) : ℝ) =
        (p : ℝ) ^ (a u) * (p : ℝ) ^ (a v) := by
    calc
      _ = (Fintype.card (ZMod (p ^ (a u)) × ZMod (p ^ (a v))) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = (p : ℝ) ^ (a u) * (p : ℝ) ^ (a v) := by
        simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul, Nat.cast_pow]
  rw [hcardH, hcardH₁] at hbound
  exact hbound

private theorem localKernel_upper_one_row {p A q d : ℕ}
    (hp : p.Prime)
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A)) (u : Fin q)
    (hrow : ∃ j, IsUnit (coeff u j))
    [Fintype (Multiplicative (Fin d → ZMod (p ^ A)))]
    [Fintype (Multiplicative ((v : Fin q) → ZMod (p ^ (a v))))]
    [Fintype (Multiplicative (ZMod (p ^ (a u))))] :
    normalizedKernelCount (localDivisibilityGroupHom a ha coeff) ≤
      (∏ v, (p : ℝ) ^ (a v)) / (p : ℝ) ^ (a u) := by
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI (v : Fin q) : NeZero (p ^ (a v)) :=
    ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  have hsurj := localCoordinate_projection_surjective hp a ha coeff u hrow
  have hbound := normalizedKernelCount_le_of_surjective_projection
    (localDivisibilityGroupHom a ha coeff) (localCoordinateProjection a u) hsurj
  have hcardH :
      (Fintype.card (Multiplicative ((v : Fin q) → ZMod (p ^ (a v)))) : ℝ) =
        ∏ v, (p : ℝ) ^ (a v) := by
    calc
      _ = (Fintype.card ((v : Fin q) → ZMod (p ^ (a v))) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = ∏ v, (Fintype.card (ZMod (p ^ (a v))) : ℝ) := by
        exact_mod_cast (Fintype.card_pi :
          Fintype.card ((v : Fin q) → ZMod (p ^ (a v))) =
            ∏ v, Fintype.card (ZMod (p ^ (a v))))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [ZMod.card]
        norm_cast
  have hcardH₁ :
      (Fintype.card (Multiplicative (ZMod (p ^ (a u)))) : ℝ) =
        (p : ℝ) ^ (a u) := by
    calc
      _ = (Fintype.card (ZMod (p ^ (a u))) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = _ := by
        rw [ZMod.card]
        norm_cast
  rw [hcardH, hcardH₁] at hbound
  exact hbound

/-- Prime-p valuation mass of a divisor law. -/
def primeValuationMass (law : TailProductLaw) (p a : ℕ) : ℝ :=
  ∑' σ : ℕ, law σ * if Nat.factorization σ p = a then 1 else 0

private def harmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

private theorem harmonicNatLaw_zero_of_not_mem (X W n : ℕ)
    (hn : n ∉ harmonicNatSupport X W) : harmonicNatLaw X W n = 0 := by
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro h
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  simp [harmonicNatLaw, hnot]

private theorem harmonicNatLaw_tsum_eq_one (X W : ℕ) (hX : 0 < X)
    (hH : 0 < harmonicNormalizer X W) :
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
      have hnIco : n ∈ Finset.Ico X (X ^ 2) := (Finset.mem_filter.mp hn).1
      have hnrange : X ≤ n ∧ n < X ^ 2 := Finset.mem_Ico.mp hnIco
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hX hnrange.1
      have hnvalid : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W :=
        ⟨hnrange.1, hnrange.2, (Finset.mem_filter.mp hn).2⟩
      have hpoint : harmonicNatLaw X W n =
          1 / ((n : ℝ) * harmonicNormalizer X W) := by
        simp [harmonicNatLaw, hnvalid.1, hnvalid.2.1, hnvalid.2.2]
      rw [hpoint]
      field_simp [ne_of_gt hnpos, ne_of_gt hH]
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [show (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W by
        simp [harmonicNormalizer, S, harmonicNatSupport]]
      exact div_self (ne_of_gt hH)

private theorem harmonicNatTupleLaw_tsum_eq_one {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    ∑' t : Fin k → ℕ, ∏ i, harmonicNatLaw (X i) W (t i) = 1 := by
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  have hzero (t : Fin k → ℕ) (ht : t ∉ T) :
      ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  rw [tsum_eq_sum (s := T) hzero]
  have hsum (i : Fin k) :
      ∑ n ∈ S i, harmonicNatLaw (X i) W n = 1 := by
    have htotal := harmonicNatLaw_tsum_eq_one (X i) W (hX i) (hH i)
    rw [tsum_eq_sum (s := S i) (fun n hn =>
      harmonicNatLaw_zero_of_not_mem (X i) W n hn)] at htotal
    exact htotal
  calc
    (∑ t ∈ T, ∏ i, harmonicNatLaw (X i) W (t i)) =
        ∏ i, ∑ n ∈ S i, harmonicNatLaw (X i) W n := by
      simpa [T] using (Finset.prod_univ_sum S
        (fun i n => harmonicNatLaw (X i) W n)).symm
    _ = 1 := by simp [hsum]

private theorem harmonicProductLaw_tsum_eq_one {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    (∑' σ : ℕ, harmonicProductLaw W X σ = 1) ∧
      (∀ σ, harmonicProductLaw W X σ ≠ 0 → Nat.Coprime σ W) := by
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let weight : (Fin k → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (X i) W (t i)
  let product : (Fin k → ℕ) → ℕ := fun t => ∏ i, t i
  have hweight_zero (t : Fin k → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (σ : ℕ) (t : Fin k → ℕ) (ht : t ∉ T) :
      (if product t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (σ : ℕ) (hσ : σ ∉ T.image product) :
      harmonicProductLaw W X σ = 0 := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
    apply Finset.sum_eq_zero
    intro t ht
    have hp : product t ≠ σ := by
      intro heq
      apply hσ
      exact Finset.mem_image.mpr ⟨t, ht, heq⟩
    simp [hp]
  have hLawEq (σ : ℕ) : harmonicProductLaw W X σ =
      ∑ t ∈ T, (if product t = σ then 1 else 0) * weight t := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
  have hcop_product (t : Fin k → ℕ) (ht : t ∈ T) : Nat.Coprime (product t) W := by
    apply Nat.coprime_fintype_prod_left_iff.mpr
    intro i
    have hi : t i ∈ harmonicNatSupport (X i) W := by
      simpa [S] using (Fintype.mem_piFinset.mp ht i)
    exact (Finset.mem_filter.mp hi).2
  have htuple : ∑ t ∈ T, weight t = 1 := by
    have h := harmonicNatTupleLaw_tsum_eq_one W X hX hH
    have hzero : ∀ t ∉ T, weight t = 0 := hweight_zero
    simpa [weight, T] using (tsum_eq_sum (s := T) hzero).symm.trans h
  constructor
  · rw [tsum_eq_sum (s := T.image product) hLawZero]
    calc
      (∑ σ ∈ T.image product, harmonicProductLaw W X σ) =
          ∑ σ ∈ T.image product, ∑ t ∈ T,
            (if product t = σ then 1 else 0) * weight t := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact hLawEq σ
      _ = ∑ t ∈ T, weight t := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t ht
            have hin : product t ∈ T.image product :=
              Finset.mem_image.mpr ⟨t, ht, rfl⟩
            simp [Finset.sum_ite_eq', hin]
      _ = 1 := htuple
  · intro σ hσ
    have himage : σ ∈ T.image product := by
      by_contra hnot
      exact hσ (hLawZero σ hnot)
    obtain ⟨t, ht, hprod⟩ := Finset.mem_image.mp himage
    rw [← hprod]
    exact hcop_product t ht

private theorem harmonicProductLaw_nonneg {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) (σ : ℕ) :
    0 ≤ harmonicProductLaw W X σ := by
  classical
  unfold harmonicProductLaw
  apply tsum_nonneg
  intro t
  by_cases hprod : ∏ i, t i = σ
  · simp only [if_pos hprod, one_mul]
    apply Finset.prod_nonneg
    intro i hi
    unfold harmonicNatLaw
    split_ifs with h
    · have htpos : 0 < t i := lt_of_lt_of_le (hX i) h.1
      have htR : (0 : ℝ) < (t i : ℝ) := by exact_mod_cast htpos
      positivity [hH i]
    · simp
  · simp [hprod]

private theorem harmonicProductLaw_primeValuationMass {k : ℕ} (W p : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (X : Fin k → ℕ)
    (hX : ∀ i, 0 < X i) (hH : ∀ i, 0 < harmonicNormalizer (X i) W) (a : ℕ) :
    primeValuationMass (harmonicProductLaw W X) p a = if a = 0 then 1 else 0 := by
  obtain ⟨htotal, hsupport⟩ := harmonicProductLaw_tsum_eq_one W X hX hH
  by_cases ha : a = 0
  · subst a
    have hterm (σ : ℕ) :
        harmonicProductLaw W X σ *
            (if Nat.factorization σ p = 0 then 1 else 0) = harmonicProductLaw W X σ := by
      by_cases hmass : harmonicProductLaw W X σ = 0
      · simp [hmass]
      · have hcopW := hsupport σ hmass
        have hcopP : Nat.Coprime σ p := hcopW.coprime_dvd_right hpW
        have hnot : ¬ p ∣ σ := by
          intro hdiv
          have hgcd : Nat.gcd σ p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcopP
          have hdvd : p ∣ Nat.gcd σ p := Nat.dvd_gcd hdiv (dvd_rfl)
          rw [hgcd] at hdvd
          exact hp.not_dvd_one hdvd
        rw [Nat.factorization_eq_zero_of_not_dvd hnot]
        simp
    unfold primeValuationMass
    calc
      (∑' σ : ℕ, harmonicProductLaw W X σ *
          (if Nat.factorization σ p = 0 then 1 else 0)) =
        ∑' σ : ℕ, harmonicProductLaw W X σ := tsum_congr hterm
      _ = 1 := htotal
  · have hterm (σ : ℕ) :
        harmonicProductLaw W X σ *
            (if Nat.factorization σ p = a then 1 else 0) = 0 := by
      by_cases hmass : harmonicProductLaw W X σ = 0
      · simp [hmass]
      · have hcopW := hsupport σ hmass
        have hcopP : Nat.Coprime σ p := hcopW.coprime_dvd_right hpW
        have hnot : ¬ p ∣ σ := by
          intro hdiv
          have hgcd : Nat.gcd σ p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcopP
          have hdvd : p ∣ Nat.gcd σ p := Nat.dvd_gcd hdiv (dvd_rfl)
          rw [hgcd] at hdvd
          exact hp.not_dvd_one hdvd
        have hval : Nat.factorization σ p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd hnot
        simp [hmass, hval, ha, eq_comm]
    unfold primeValuationMass
    have hfun : (fun σ : ℕ => harmonicProductLaw W X σ *
        (if Nat.factorization σ p = a then 1 else 0)) = fun _ => 0 := by
      funext σ
      exact hterm σ
    rw [hfun]
    simp [ha]

private theorem harmonicNormalizer_pos_of_cutoff (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) : 0 < harmonicNormalizer X W := by
  have h := OAI.RawHarmonicProbability.mass_pos X W hW hX
  simpa [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
    Finset.sum_filter, one_div, Nat.coprime_comm] using h

private theorem divisorTemplateLaw_coprime_primorial {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (u : Fin q) (σ : ℕ)
    (hσ : divisorTemplateLaw S.core.parameters N (D.divisor u) σ ≠ 0) :
    Nat.Coprime σ (primorial (N + 1)) := by
  let W := primorial (N + 1)
  let X : Fin (D.divisor u).arity → ℕ :=
    fun j => S.core.parameters.X N ((D.divisor u).cutoff j)
  have hW : 0 < W := by dsimp [W]; exact primorial_pos _
  have hX (j : Fin (D.divisor u).arity) : 0 < X j := by
    dsimp [X]
    exact S.core.parameters.Xpos N ((D.divisor u).cutoff j)
  have hH (j : Fin (D.divisor u).arity) : 0 < harmonicNormalizer (X j) W := by
    apply harmonicNormalizer_pos_of_cutoff (X j) W hW
    dsimp [X, W]
    exact S.gapStage.valid_raw_cutoffs N ((D.divisor u).cutoff j)
  have hsupport :=
    (harmonicProductLaw_tsum_eq_one W X hX hH).2
  apply hsupport σ
  change harmonicProductLaw W X σ ≠ 0
  exact hσ

private theorem divisorTuple_rowDenominators_coprime
    {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (slots : Fin m → ℕ) (σ : Fin q → ℕ)
    (hgood : D.goodDomain N slots)
    (hσ : ∀ u, divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u) ≠ 0) :
    ∀ u j, Nat.Coprime (D.rowCoeff N slots u j).den (∏ v, σ v) := by
  have hσpos (u : Fin q) : 1 ≤ σ u := D.divisor_positive N u (σ u) (hσ u)
  have hσbound (u : Fin q) : σ u ≤ D.V N := D.divisor_bounded N u (σ u) (hσ u)
  have hσcop (u : Fin q) : Nat.Coprime (σ u) (primorial (N + 1)) :=
    divisorTemplateLaw_coprime_primorial D N u (σ u) (hσ u)
  exact rowCoefficient_den_coprime_divisorProduct D N slots σ hgood hσpos hσbound hσcop

private theorem harmonicUnitPrefix_bound (X W : ℕ) (hW : 0 < W) (hX : 2 ≤ X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) :
    (∑ n ∈ Finset.Ico 1 (X ^ 2),
      if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≤
      (Nat.totient W : ℝ) / W * (2 * Real.log (X : ℝ)) + Nat.totient W := by
  have hsampling := sampling_pointwise_claim X W hW hX hlog
  have hperiodic := hsampling.periodic_harmonic 1 0 1 (X ^ 2 : ℕ)
    (by simp) (by omega) (by norm_num)
    (by
      have hXr : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have hX2 : (1 : ℝ) < (X : ℝ) ^ 2 := by nlinarith
      simpa [Nat.cast_pow] using hX2)
  let f : ℕ → ℝ := fun n =>
    if (1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X ^ 2 : ℕ) ∧
        Nat.Coprime n W ∧ n % 1 = 0 then 1 / (n : ℝ) else 0
  have hzero : ∀ n ∉ Finset.Ico 1 (X ^ 2), f n = 0 := by
    intro n hn
    have hnot : ¬ (1 ≤ n ∧ n < X ^ 2) := by
      intro h
      apply hn
      exact Finset.mem_Ico.mpr h
    have hnotR : ¬ ((1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X ^ 2 : ℕ)) := by
      intro h
      apply hnot
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hcond :
        ¬ ((1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X ^ 2 : ℕ) ∧
          Nat.Coprime n W ∧ n % 1 = 0) := by
      intro h
      exact hnotR ⟨h.1, h.2.1⟩
    change (if (1 : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (X ^ 2 : ℕ) ∧
      Nat.Coprime n W ∧ n % 1 = 0 then 1 / (n : ℝ) else 0) = 0
    rw [if_neg hcond]
  have hsum :
      (∑' n : ℕ, f n) =
        ∑ n ∈ Finset.Ico 1 (X ^ 2),
          if Nat.Coprime n W then 1 / (n : ℝ) else 0 := by
    rw [tsum_eq_sum (s := Finset.Ico 1 (X ^ 2)) hzero]
    apply Finset.sum_congr rfl
    intro n hn
    have hnIco : 1 ≤ n ∧ n < X ^ 2 := Finset.mem_Ico.mp hn
    have h2R : (n : ℝ) < (X ^ 2 : ℝ) := by exact_mod_cast hnIco.2
    simp [f, hnIco.1, h2R, Nat.mod_one]
  have hperiodic' :
      |(∑' n : ℕ, f n) -
        (Nat.totient W : ℝ) / W * (2 * Real.log (X : ℝ))| ≤
        (Nat.totient W : ℝ) := by
    simpa [f, Nat.mod_one, Real.log_pow, Nat.cast_pow] using hperiodic
  rw [hsum] at hperiodic'
  have hupper := (abs_le.mp hperiodic').2
  linarith

private theorem harmonicUnitMultiples_sum_le (X W k : ℕ) (hX : 0 < X)
    (hk : 0 < k) (hcop : Nat.Coprime k W) :
    (∑ n ∈ ((Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)).filter
        (fun n => k ∣ n), 1 / (n : ℝ)) ≤
      (1 / (k : ℝ)) *
        (∑ m ∈ Finset.Ico 1 (X ^ 2),
          if Nat.Coprime m W then 1 / (m : ℝ) else 0) := by
  classical
  let S := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  let T := S.filter (fun n => k ∣ n)
  let f : ℕ → ℕ := fun n => n / k
  let U := (Finset.Ico 1 (X ^ 2)).filter (fun m => Nat.Coprime m W)
  have hmul (n : ℕ) (hn : n ∈ T) : k * f n = n := by
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  have hinj : Set.InjOn f (↑T : Set ℕ) := by
    intro n hn m hm hnm
    have hnT : n ∈ T := hn
    have hmT : m ∈ T := hm
    calc
      n = k * f n := (hmul n hnT).symm
      _ = k * f m := congrArg (fun z => k * z) hnm
      _ = m := hmul m hmT
  have hsubset : T.image f ⊆ U := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hnT, rfl⟩
    have hnS : n ∈ S := (Finset.mem_filter.mp hnT).1
    have hdiv : k ∣ n := (Finset.mem_filter.mp hnT).2
    have hnrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hnS).1
    have hcopn := (Finset.mem_filter.mp hnS).2
    have hmuln := hmul n hnT
    have hmne : n / k ≠ 0 := by
      intro hm0
      have hnpos : 0 < n := lt_of_lt_of_le hX hnrange.1
      apply (Nat.ne_of_gt hnpos)
      rw [← hmuln]
      simp [f, hm0]
    have hmpos : 1 ≤ n / k := Nat.one_le_iff_ne_zero.mpr hmne
    have hmlt : n / k < X ^ 2 := lt_of_le_of_lt (Nat.div_le_self _ _) hnrange.2
    have hcopprod : Nat.Coprime (k * (n / k)) W := by
      simpa [f, hmuln] using hcopn
    have hcopm : Nat.Coprime (n / k) W :=
      (Nat.coprime_mul_iff_left.mp hcopprod).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hmpos, hmlt⟩, hcopm⟩
  have hsumImage :
      (∑ n ∈ T, 1 / (n : ℝ)) =
        (1 / (k : ℝ)) * ∑ m ∈ T.image f, 1 / (m : ℝ) := by
    calc
      (∑ n ∈ T, 1 / (n : ℝ)) =
          ∑ n ∈ T, (1 / (k : ℝ)) * (1 / (f n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hnT
        have hmuln := hmul n hnT
        have hnrange := Finset.mem_Ico.mp
          ((Finset.mem_filter.mp (Finset.mem_filter.mp hnT).1).1)
        have hmne : f n ≠ 0 := by
          intro hzero
          have hnpos : 0 < n := lt_of_lt_of_le hX hnrange.1
          apply (Nat.ne_of_gt hnpos)
          rw [← hmuln]
          simp [f, hzero]
        have hnEq : (n : ℝ) = (k : ℝ) * (f n : ℝ) := by
          exact_mod_cast hmuln.symm
        calc
          1 / (n : ℝ) = 1 / ((k : ℝ) * (f n : ℝ)) := by rw [hnEq]
          _ = (1 / (k : ℝ)) * (1 / (f n : ℝ)) := by
            field_simp [ne_of_gt (Nat.cast_pos.mpr hk),
              ne_of_gt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmne))]
      _ = (1 / (k : ℝ)) * ∑ n ∈ T, 1 / (f n : ℝ) := by
        rw [← Finset.mul_sum]
      _ = (1 / (k : ℝ)) * ∑ m ∈ T.image f, 1 / (m : ℝ) := by
        congr 1
        exact (Finset.sum_image (s := T) (g := f)
          (f := fun m : ℕ => 1 / (m : ℝ)) hinj).symm
  have hsumSubset :
      (∑ m ∈ T.image f, 1 / (m : ℝ)) ≤
        ∑ m ∈ U, if Nat.Coprime m W then 1 / (m : ℝ) else 0 := by
    calc
      (∑ m ∈ T.image f, 1 / (m : ℝ)) ≤ ∑ m ∈ U, 1 / (m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro m hmU hmNot
          positivity)
      _ = ∑ m ∈ U, if Nat.Coprime m W then 1 / (m : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro m hmU
        simp [U, (Finset.mem_filter.mp hmU).2]
  have hUeq :
      (∑ m ∈ U, if Nat.Coprime m W then 1 / (m : ℝ) else 0) =
        ∑ m ∈ Finset.Ico 1 (X ^ 2),
          if Nat.Coprime m W then 1 / (m : ℝ) else 0 := by
    dsimp [U]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hcopm : Nat.Coprime m W <;> simp [hcopm]
  calc
    (∑ n ∈ T, 1 / (n : ℝ)) =
        (1 / (k : ℝ)) * ∑ m ∈ T.image f, 1 / (m : ℝ) := hsumImage
    _ ≤ (1 / (k : ℝ)) *
        (∑ m ∈ U, if Nat.Coprime m W then 1 / (m : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left hsumSubset (by positivity)
    _ = _ := by rw [hUeq]

private theorem harmonicNatDivisibilityMass_le (X W k : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlogLarge : 4 * (W : ℝ) ≤ Real.log (X : ℝ))
    (hk : 0 < k) (hcop : Nat.Coprime k W) :
    (∑' n : ℕ, harmonicNatLaw X W n * if k ∣ n then 1 else 0) ≤
      6 / (k : ℝ) := by
  classical
  let H := harmonicNormalizer X W
  let θ : ℝ := (Nat.totient W : ℝ) / W
  have hWone : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hW)
  have hXpos : 0 < X := by omega
  have hXtwo : 2 ≤ X := by omega
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hXpos
  have hWreal : 0 < (W : ℝ) := by exact_mod_cast hW
  have hWrealone : 1 ≤ (W : ℝ) := by exact_mod_cast hWone
  have hfourWleX : 4 * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hWX : (W : ℝ) / X ≤ 1 / 4 := by
    rw [div_le_iff₀ hXreal]
    nlinarith
  have hlogLower : 4 ≤ Real.log (X : ℝ) := by nlinarith [hlogLarge]
  have hlog : Real.log (X : ℝ) > (W : ℝ) / X := by linarith
  have hnormPos : 0 < H := by
    dsimp [H]
    exact harmonicNormalizer_pos_of_cutoff X W hW hX
  have hsample := sampling_pointwise_claim X W hW hXtwo hlog
  have hnormError := hsample.normalizer hXtwo hlog
  have hphiPos : 0 < (Nat.totient W : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact div_pos hphiPos hWreal
  have hφ : (Nat.totient W : ℝ) = θ * (W : ℝ) := by
    dsimp [θ]
    field_simp [ne_of_gt hWreal]
  have hφX : (Nat.totient W : ℝ) / X = θ * ((W : ℝ) / X) := by
    rw [hφ]
    field_simp [ne_of_gt hXreal]
  have hnormLower : θ * (Real.log (X : ℝ) - (W : ℝ) / X) ≤ H := by
    have hdev := (abs_le.mp hnormError).1
    dsimp [H, θ] at hdev ⊢
    rw [hφX] at hdev
    nlinarith
  have hprefix := harmonicUnitPrefix_bound X W hW hXtwo hlog
  have hprefixUpper :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≤
        θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := by
    calc
      _ ≤ (Nat.totient W : ℝ) / W * (2 * Real.log (X : ℝ)) + Nat.totient W := hprefix
      _ = θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := by
        rw [hφ]
        dsimp [θ]
        field_simp [ne_of_gt hWreal]
  have hratio :
      2 * Real.log (X : ℝ) + (W : ℝ) ≤
        6 * (Real.log (X : ℝ) - (W : ℝ) / X) := by
    nlinarith [hlogLarge, hWX, hWrealone]
  have hprefix6 :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≤ 6 * H := by
    calc
      _ ≤ θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := hprefixUpper
      _ ≤ θ * (6 * (Real.log (X : ℝ) - (W : ℝ) / X)) :=
        mul_le_mul_of_nonneg_left hratio hθpos.le
      _ = 6 * (θ * (Real.log (X : ℝ) - (W : ℝ) / X)) := by ring
      _ ≤ 6 * H := mul_le_mul_of_nonneg_left hnormLower (by norm_num)
  have hprefixDiv :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) / H ≤ 6 :=
    (div_le_iff₀ hnormPos).2 (by nlinarith [hprefix6])
  have hdivMass := harmonicUnitMultiples_sum_le X W k hXpos hk hcop
  let S := harmonicNatSupport X W
  let T := S.filter (fun n => k ∣ n)
  have hzero (n : ℕ) (hn : n ∉ S) :
      harmonicNatLaw X W n * (if k ∣ n then 1 else 0) = 0 := by
    rw [harmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn)]
    simp
  have hmassEq :
      (∑' n : ℕ, harmonicNatLaw X W n * (if k ∣ n then 1 else 0)) =
        ∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0) := by
    rw [tsum_eq_sum (s := S) hzero]
  have hfilter :
      (∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0)) =
        ∑ n ∈ T, harmonicNatLaw X W n := by
    dsimp [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : k ∣ n <;> simp [hd]
  have hTlaw :
      (∑ n ∈ T, harmonicNatLaw X W n) =
        (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := by
    calc
      (∑ n ∈ T, harmonicNatLaw X W n) =
          ∑ n ∈ T, (1 / H) * (1 / (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hnrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hnS).1
        have hcopn := (Finset.mem_filter.mp hnS).2
        have hnpos : 0 < n := lt_of_lt_of_le hXpos hnrange.1
        have hpoint : harmonicNatLaw X W n = 1 / ((n : ℝ) * H) := by
          simp [harmonicNatLaw, H, hnrange.1, hnrange.2, hcopn]
        rw [hpoint]
        field_simp [ne_of_gt hnormPos, ne_of_gt (Nat.cast_pos.mpr hnpos)]
      _ = (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := by rw [← Finset.mul_sum]
  calc
    (∑' n : ℕ, harmonicNatLaw X W n * if k ∣ n then 1 else 0) =
        ∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0) := hmassEq
    _ = ∑ n ∈ T, harmonicNatLaw X W n := hfilter
    _ = (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := hTlaw
    _ ≤ (1 / H) * ((1 / (k : ℝ)) *
          (∑ n ∈ Finset.Ico 1 (X ^ 2),
            if Nat.Coprime n W then 1 / (n : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hdivMass (by positivity)
    _ = (1 / (k : ℝ)) *
          ((∑ n ∈ Finset.Ico 1 (X ^ 2),
            if Nat.Coprime n W then 1 / (n : ℝ) else 0) / H) := by ring
    _ ≤ (1 / (k : ℝ)) * 6 := mul_le_mul_of_nonneg_left hprefixDiv (by positivity)
    _ = 6 / (k : ℝ) := by ring

private theorem primePowerProduct_dvd_of_factorization {n : ℕ} (hn : n ≠ 0)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (a : ℕ → ℕ)
    (hval : ∀ p ∈ P, Nat.factorization n p = a p) :
    (∏ p ∈ P, p ^ a p) ∣ n := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hpnot ih =>
    have hpPow : p ^ a p ∣ n := by
      apply (hprime p (Finset.mem_insert_self p P)).pow_dvd_iff_le_factorization hn |>.2
      rw [hval p (Finset.mem_insert_self p P)]
    have hqVal : ∀ q (hq : q ∈ P),
        Nat.factorization n q = a q := by
      intro q hq
      exact hval q (Finset.mem_insert_of_mem hq)
    have hprimeP : ∀ q ∈ P, q.Prime := by
      intro q hq
      exact hprime q (Finset.mem_insert_of_mem hq)
    have hPdiv : (∏ q ∈ P, q ^ a q) ∣ n := ih hprimeP hqVal
    have hcop :
        Nat.Coprime (p ^ a p) (∏ q ∈ P, q ^ a q) := by
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      apply Nat.coprime_pow_primes (a p) (a q)
        (hprime p (Finset.mem_insert_self p P))
        (hprime q (Finset.mem_insert_of_mem hq))
      intro heq
      subst q
      exact hpnot hq
    rw [Finset.prod_insert hpnot]
    exact hcop.mul_dvd_of_dvd_of_dvd hpPow hPdiv

private theorem harmonicNatPrimeVectorMass_le (X W : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, Nat.Coprime p W)
    (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlogLarge : 4 * (W : ℝ) ≤ Real.log (X : ℝ))
    (a : ℕ → ℕ) :
    (∑' n : ℕ, harmonicNatLaw X W n *
      (if ∀ p ∈ P, Nat.factorization n p = a p then 1 else 0)) ≤
      6 / ∏ p ∈ P, (p : ℝ) ^ (a p) := by
  classical
  let K : ℕ := ∏ p ∈ P, p ^ a p
  have hKpos : 0 < K := by
    dsimp [K]
    apply Finset.prod_pos
    intro p hp
    exact Nat.pow_pos (hprime p hp).pos
  have hKcop : Nat.Coprime K W := by
    dsimp [K]
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (hcop p hp).pow_left _
  have hpoint (n : ℕ) :
      harmonicNatLaw X W n *
          (if ∀ p ∈ P, Nat.factorization n p = a p then 1 else 0) ≤
        harmonicNatLaw X W n * (if K ∣ n then 1 else 0) := by
    by_cases hval : ∀ p ∈ P, Nat.factorization n p = a p
    · have hdiv : K ∣ n := by
        by_cases hn : n = 0
        · simp [hn]
        · simpa [K] using primePowerProduct_dvd_of_factorization hn P hprime a hval
      simp only [if_pos hval, if_pos hdiv, mul_one]
      exact le_rfl
    · have hnonneg : 0 ≤ harmonicNatLaw X W n := by
        unfold harmonicNatLaw
        split_ifs with h
        · have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < X) h.1
          positivity [harmonicNormalizer_pos_of_cutoff X W hW hX]
        · simp
      by_cases hdiv : K ∣ n
      · simp [hval, hdiv, hnonneg]
      · simp [hval, hdiv]
  have hLawSummable : Summable (fun n : ℕ => harmonicNatLaw X W n) := by
    apply summable_of_ne_finset_zero (s := harmonicNatSupport X W)
    intro n hn
    exact harmonicNatLaw_zero_of_not_mem X W n hn
  have hLawNonneg (n : ℕ) : 0 ≤ harmonicNatLaw X W n := by
    unfold harmonicNatLaw
    split_ifs with h
    · have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < X) h.1
      positivity [harmonicNormalizer_pos_of_cutoff X W hW hX]
    · simp
  have hLhsSummable : Summable (fun n : ℕ => harmonicNatLaw X W n *
      (if ∀ p ∈ P, Nat.factorization n p = a p then 1 else 0)) := by
    apply hLawSummable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (hLawNonneg n) (by split_ifs <;> norm_num)
    · intro n
      by_cases hval : ∀ p ∈ P, Nat.factorization n p = a p
      · simp only [if_pos hval, mul_one, le_rfl]
      · simp [hval, hLawNonneg n]
  have hRhsSummable : Summable (fun n : ℕ =>
      harmonicNatLaw X W n * (if K ∣ n then 1 else 0)) := by
    apply hLawSummable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (hLawNonneg n) (by split_ifs <;> norm_num)
    · intro n
      by_cases hdiv : K ∣ n <;> simp [hdiv, hLawNonneg n]
  have hmassLE := Summable.tsum_le_tsum hpoint hLhsSummable hRhsSummable
  calc
    (∑' n : ℕ, harmonicNatLaw X W n *
      (if ∀ p ∈ P, Nat.factorization n p = a p then 1 else 0)) ≤
        (6 : ℝ) / (K : ℝ) := by
          have hdiv := harmonicNatDivisibilityMass_le X W K hW hX hlogLarge hKpos hKcop
          exact hmassLE.trans hdiv
    _ = 6 / ∏ p ∈ P, (p : ℝ) ^ (a p) := by
      simp [K, Nat.cast_prod, Nat.cast_pow]

private theorem harmonicNatValuationMass_le (X W p a : ℕ)
    (hW : 0 < W) (hX : 4 * W ≤ X)
    (hlogLarge : 4 * (W : ℝ) ≤ Real.log (X : ℝ))
    (hp : p.Prime) (hcop : Nat.Coprime (p ^ a) W) :
    primeValuationMass (fun n => harmonicNatLaw X W n) p a ≤
      6 / (p : ℝ) ^ a := by
  classical
  let k := p ^ a
  let H := harmonicNormalizer X W
  let θ : ℝ := (Nat.totient W : ℝ) / W
  have hWone : 1 ≤ W := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hW)
  have hXpos : 0 < X := by omega
  have hXtwo : 2 ≤ X := by omega
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hXpos
  have hWreal : 0 < (W : ℝ) := by exact_mod_cast hW
  have hWrealone : 1 ≤ (W : ℝ) := by exact_mod_cast hWone
  have hfourWleX : 4 * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hWX : (W : ℝ) / X ≤ 1 / 4 := by
    rw [div_le_iff₀ hXreal]
    nlinarith
  have hlogLower : 4 ≤ Real.log (X : ℝ) := by nlinarith [hlogLarge]
  have hlog : Real.log (X : ℝ) > (W : ℝ) / X := by linarith
  have hnormPos : 0 < H := by
    dsimp [H]
    exact harmonicNormalizer_pos_of_cutoff X W hW hX
  have hsample := sampling_pointwise_claim X W hW hXtwo hlog
  have hnormError := hsample.normalizer hXtwo hlog
  have hphiPos : 0 < (Nat.totient W : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact div_pos hphiPos hWreal
  have hφ : (Nat.totient W : ℝ) = θ * (W : ℝ) := by
    dsimp [θ]
    field_simp [ne_of_gt hWreal]
  have hφX : (Nat.totient W : ℝ) / X = θ * ((W : ℝ) / X) := by
    rw [hφ]
    field_simp [ne_of_gt hXreal]
  have hnormLower : θ * (Real.log (X : ℝ) - (W : ℝ) / X) ≤ H := by
    have hdev := (abs_le.mp hnormError).1
    dsimp [H, θ] at hdev ⊢
    rw [hφX] at hdev
    nlinarith
  have hprefix := harmonicUnitPrefix_bound X W hW hXtwo hlog
  have hprefixUpper :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≤
        θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := by
    calc
      _ ≤ (Nat.totient W : ℝ) / W * (2 * Real.log (X : ℝ)) + Nat.totient W := hprefix
      _ = θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := by
        rw [hφ]
        dsimp [θ]
        field_simp [ne_of_gt hWreal]
  have hratio :
      2 * Real.log (X : ℝ) + (W : ℝ) ≤
        6 * (Real.log (X : ℝ) - (W : ℝ) / X) := by
    nlinarith [hlogLarge, hWX, hWrealone]
  have hprefix6 :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≤ 6 * H := by
    calc
      _ ≤ θ * (2 * Real.log (X : ℝ) + (W : ℝ)) := hprefixUpper
      _ ≤ θ * (6 * (Real.log (X : ℝ) - (W : ℝ) / X)) :=
        mul_le_mul_of_nonneg_left hratio hθpos.le
      _ = 6 * (θ * (Real.log (X : ℝ) - (W : ℝ) / X)) := by ring
      _ ≤ 6 * H := mul_le_mul_of_nonneg_left hnormLower (by norm_num)
  have hprefixDiv :
      (∑ n ∈ Finset.Ico 1 (X ^ 2),
        if Nat.Coprime n W then 1 / (n : ℝ) else 0) / H ≤ 6 :=
    (div_le_iff₀ hnormPos).2 (by nlinarith [hprefix6])
  have hkpos : 0 < k := by dsimp [k]; exact Nat.pow_pos hp.pos
  have hkp : (k : ℝ) = (p : ℝ) ^ a := by simp [k, Nat.cast_pow]
  have hdivMass := harmonicUnitMultiples_sum_le X W k hXpos hkpos hcop
  let S := harmonicNatSupport X W
  let T := S.filter (fun n => k ∣ n)
  have hzero (n : ℕ) (hn : n ∉ S) :
      harmonicNatLaw X W n * (if Nat.factorization n p = a then 1 else 0) = 0 := by
    rw [harmonicNatLaw_zero_of_not_mem X W n (by simpa [S] using hn)]
    simp
  have hmassEq :
      primeValuationMass (fun n => harmonicNatLaw X W n) p a =
        ∑ n ∈ S, harmonicNatLaw X W n * (if Nat.factorization n p = a then 1 else 0) := by
    unfold primeValuationMass
    rw [tsum_eq_sum (s := S) hzero]
  have hfacDiv (n : ℕ) (hn : n ∈ S)
      (hv : Nat.factorization n p = a) : k ∣ n := by
    have hnrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    have hnpos : 0 < n := lt_of_lt_of_le hXpos hnrange.1
    apply (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hnpos)).2
    rw [hv]
  have hμnonneg (n : ℕ) : 0 ≤ harmonicNatLaw X W n := by
    unfold harmonicNatLaw
    split_ifs with h
    · have hnpos : 0 < n := lt_of_lt_of_le hXpos h.1
      positivity
    · simp
  have hcompare :
      (∑ n ∈ S, harmonicNatLaw X W n *
        (if Nat.factorization n p = a then 1 else 0)) ≤
      ∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0) := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hv : Nat.factorization n p = a
    · have hd := hfacDiv n hn hv
      simp [hv, hd]
    · simp [hv]
      by_cases hd : k ∣ n <;> simp [hd, hμnonneg n]
  have hfilter :
      (∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0)) =
        ∑ n ∈ T, harmonicNatLaw X W n := by
    dsimp [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : k ∣ n <;> simp [hd]
  have hTlaw :
      (∑ n ∈ T, harmonicNatLaw X W n) =
        (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := by
    calc
      (∑ n ∈ T, harmonicNatLaw X W n) =
          ∑ n ∈ T, (1 / H) * (1 / (n : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
        have hnrange := Finset.mem_Ico.mp (Finset.mem_filter.mp hnS).1
        have hcopn := (Finset.mem_filter.mp hnS).2
        have hnpos : 0 < n := lt_of_lt_of_le hXpos hnrange.1
        have hpoint : harmonicNatLaw X W n =
            1 / ((n : ℝ) * H) := by
          simp [harmonicNatLaw, H, hnrange.1, hnrange.2, hcopn]
        rw [hpoint]
        field_simp [ne_of_gt hnormPos, ne_of_gt (Nat.cast_pos.mpr hnpos)]
      _ = (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := by rw [← Finset.mul_sum]
  calc
    primeValuationMass (fun n => harmonicNatLaw X W n) p a =
        ∑ n ∈ S, harmonicNatLaw X W n *
          (if Nat.factorization n p = a then 1 else 0) := hmassEq
    _ ≤ ∑ n ∈ S, harmonicNatLaw X W n * (if k ∣ n then 1 else 0) := hcompare
    _ = ∑ n ∈ T, harmonicNatLaw X W n := hfilter
    _ = (1 / H) * ∑ n ∈ T, 1 / (n : ℝ) := hTlaw
    _ ≤ (1 / H) * ((1 / (k : ℝ)) *
          (∑ n ∈ Finset.Ico 1 (X ^ 2),
            if Nat.Coprime n W then 1 / (n : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left hdivMass (by positivity)
    _ = (1 / (k : ℝ)) *
          ((∑ n ∈ Finset.Ico 1 (X ^ 2),
            if Nat.Coprime n W then 1 / (n : ℝ) else 0) / H) := by ring
    _ ≤ (1 / (k : ℝ)) * 6 := mul_le_mul_of_nonneg_left hprefixDiv (by positivity)
    _ = 6 / (p : ℝ) ^ a := by rw [hkp]; ring

private theorem harmonicProductLaw_primeValuationMass_eq {k : ℕ} (W p a : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    primeValuationMass (harmonicProductLaw W X) p a =
      ∑' t : Fin k → ℕ,
        (∏ i, harmonicNatLaw (X i) W (t i)) *
          (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) := by
  classical
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let product : (Fin k → ℕ) → ℕ := fun t => ∏ i, t i
  let weight : (Fin k → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (X i) W (t i)
  have hweight_zero (t : Fin k → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (σ : ℕ) (t : Fin k → ℕ) (ht : t ∉ T) :
      (if product t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (σ : ℕ) (hσ : σ ∉ T.image product) :
      harmonicProductLaw W X σ = 0 := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
    apply Finset.sum_eq_zero
    intro t ht
    have hne : product t ≠ σ := by
      intro heq
      exact hσ (Finset.mem_image.mpr ⟨t, ht, heq⟩)
    simp [hne]
  have hLawEq (σ : ℕ) :
      harmonicProductLaw W X σ =
        ∑ t ∈ T, (if product t = σ then 1 else 0) * weight t := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
  have hfacprod (t : Fin k → ℕ) (ht : t ∈ T) :
      Nat.factorization (product t) p = ∑ i, Nat.factorization (t i) p := by
    have hnonzero : ∀ i ∈ (Finset.univ : Finset (Fin k)), t i ≠ 0 := by
      intro i hi
      have hiS : t i ∈ S i := by simpa [S] using (Fintype.mem_piFinset.mp ht i)
      have hiRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hiS).1
      exact Nat.ne_of_gt (lt_of_lt_of_le (hX i) hiRange.1)
    have hfactor := Nat.factorization_prod hnonzero
    have hcoord := congrArg (fun z : ℕ →₀ ℕ => z p) hfactor
    simpa [Finsupp.sum_apply] using hcoord
  have hmassFinite :
      primeValuationMass (harmonicProductLaw W X) p a =
        ∑ t ∈ T, weight t *
          (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) := by
    have hmassZero (σ : ℕ) (hσ : σ ∉ T.image product) :
        harmonicProductLaw W X σ *
          (if Nat.factorization σ p = a then 1 else 0) = 0 := by
      rw [hLawZero σ hσ]
      simp
    unfold primeValuationMass
    rw [tsum_eq_sum (s := T.image product) hmassZero]
    have hcollapse (t : Fin k → ℕ) (ht : t ∈ T) :
        (∑ σ ∈ T.image product,
          ((if product t = σ then 1 else 0) * weight t) *
            (if Nat.factorization σ p = a then 1 else 0)) =
          weight t * (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) := by
      have hprodMem : product t ∈ T.image product :=
        Finset.mem_image.mpr ⟨t, ht, rfl⟩
      calc
        _ = ∑ σ ∈ T.image product,
            if σ = product t then
              weight t * (if Nat.factorization (product t) p = a then 1 else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          by_cases heq : σ = product t
          · subst σ
            simp
          · simp [heq, eq_comm]
        _ = _ := by simp [Finset.sum_ite_eq', hprodMem, hfacprod t ht]
    calc
      (∑ σ ∈ T.image product,
          harmonicProductLaw W X σ * (if Nat.factorization σ p = a then 1 else 0)) =
        ∑ σ ∈ T.image product,
          (∑ t ∈ T, (if product t = σ then 1 else 0) * weight t) *
            (if Nat.factorization σ p = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [hLawEq σ]
      _ = ∑ σ ∈ T.image product, ∑ t ∈ T,
          ((if product t = σ then 1 else 0) * weight t) *
            (if Nat.factorization σ p = a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [Finset.sum_mul]
      _ = ∑ t ∈ T, ∑ σ ∈ T.image product,
          ((if product t = σ then 1 else 0) * weight t) *
            (if Nat.factorization σ p = a then 1 else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ t ∈ T, weight t *
          (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hcollapse t ht
  have htermzero (t : Fin k → ℕ) (ht : t ∉ T) :
      weight t * (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) = 0 := by
    simp [hweight_zero t ht]
  calc
    primeValuationMass (harmonicProductLaw W X) p a =
        ∑ t ∈ T, weight t *
          (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) := hmassFinite
    _ = ∑' t : Fin k → ℕ,
        weight t * (if (∑ i, Nat.factorization (t i) p) = a then 1 else 0) :=
      (tsum_eq_sum (s := T) htermzero).symm

private theorem harmonicProductLaw_primeVectorMass_eq {k : ℕ} (W : ℕ)
    (P : Finset ℕ) (a : ℕ → ℕ) (X : Fin k → ℕ)
    (hX : ∀ i, 0 < X i) (hH : ∀ i, 0 < harmonicNormalizer (X i) W) :
    (∑' σ : ℕ, harmonicProductLaw W X σ *
      (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) =
      ∑' t : Fin k → ℕ,
        (∏ i, harmonicNatLaw (X i) W (t i)) *
          (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := by
  classical
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let product : (Fin k → ℕ) → ℕ := fun t => ∏ i, t i
  let weight : (Fin k → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (X i) W (t i)
  have hweight_zero (t : Fin k → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 :=
      harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero_out (σ : ℕ) (t : Fin k → ℕ) (ht : t ∉ T) :
      (if product t = σ then 1 else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawZero (σ : ℕ) (hσ : σ ∉ T.image product) :
      harmonicProductLaw W X σ = 0 := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
    apply Finset.sum_eq_zero
    intro t ht
    have hne : product t ≠ σ := by
      intro heq
      exact hσ (Finset.mem_image.mpr ⟨t, ht, heq⟩)
    simp [hne]
  have hLawEq (σ : ℕ) : harmonicProductLaw W X σ =
      ∑ t ∈ T, (if product t = σ then 1 else 0) * weight t := by
    unfold harmonicProductLaw
    rw [tsum_eq_sum (s := T) (hterm_zero_out σ)]
  have hfacprod (t : Fin k → ℕ) (ht : t ∈ T) (p : ℕ) :
      Nat.factorization (product t) p = ∑ i, Nat.factorization (t i) p := by
    have hnonzero : ∀ i ∈ (Finset.univ : Finset (Fin k)), t i ≠ 0 := by
      intro i hi
      have hiS : t i ∈ S i := by simpa [S] using (Fintype.mem_piFinset.mp ht i)
      have hiRange := Finset.mem_Ico.mp (Finset.mem_filter.mp hiS).1
      exact Nat.ne_of_gt (lt_of_lt_of_le (hX i) hiRange.1)
    have hfactor := Nat.factorization_prod hnonzero
    have hcoord := congrArg (fun z : ℕ →₀ ℕ => z p) hfactor
    simpa [Finsupp.sum_apply] using hcoord
  have hmassFinite :
      (∑' σ : ℕ, harmonicProductLaw W X σ *
        (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) =
        ∑ t ∈ T, weight t *
          (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := by
    have hmassZero (σ : ℕ) (hσ : σ ∉ T.image product) :
        harmonicProductLaw W X σ *
          (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0) = 0 := by
      rw [hLawZero σ hσ]
      simp
    rw [tsum_eq_sum (s := T.image product) hmassZero]
    have hcollapse (t : Fin k → ℕ) (ht : t ∈ T) :
        (∑ σ ∈ T.image product,
          ((if product t = σ then 1 else 0) * weight t) *
            (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) =
          weight t *
            (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := by
      have hprodMem : product t ∈ T.image product :=
        Finset.mem_image.mpr ⟨t, ht, rfl⟩
      have hfac (p : ℕ) (hp : p ∈ P) :
          Nat.factorization (product t) p = ∑ i, Nat.factorization (t i) p :=
        hfacprod t ht p
      have hcond :
          (∀ p ∈ P, Nat.factorization (product t) p = a p) ↔
            (∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p) := by
        constructor
        · intro h p hp
          calc
            (∑ i, Nat.factorization (t i) p) = Nat.factorization (product t) p :=
              (hfac p hp).symm
            _ = a p := h p hp
        · intro h p hp
          calc
            Nat.factorization (product t) p = ∑ i, Nat.factorization (t i) p :=
              hfac p hp
            _ = a p := h p hp
      calc
        _ = ∑ σ ∈ T.image product,
            if σ = product t then
              weight t * (if ∀ p ∈ P,
                Nat.factorization (product t) p = a p then 1 else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          by_cases heq : σ = product t
          · subst σ
            simp
          · simp [heq, eq_comm]
        _ = _ := by
          simp [Finset.sum_ite_eq', hprodMem, hcond]
    calc
      (∑ σ ∈ T.image product,
          harmonicProductLaw W X σ *
            (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) =
        ∑ σ ∈ T.image product,
          (∑ t ∈ T, (if product t = σ then 1 else 0) * weight t) *
            (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [hLawEq σ]
      _ = ∑ σ ∈ T.image product, ∑ t ∈ T,
          ((if product t = σ then 1 else 0) * weight t) *
            (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [Finset.sum_mul]
      _ = ∑ t ∈ T, ∑ σ ∈ T.image product,
          ((if product t = σ then 1 else 0) * weight t) *
            (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ t ∈ T, weight t *
          (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hcollapse t ht
  have htermzero (t : Fin k → ℕ) (ht : t ∉ T) :
      weight t * (if ∀ p ∈ P,
        (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) = 0 := by
    simp [hweight_zero t ht]
  calc
    (∑' σ : ℕ, harmonicProductLaw W X σ *
      (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) =
        ∑ t ∈ T, weight t *
          (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := hmassFinite
    _ = ∑' t : Fin k → ℕ, weight t *
        (if ∀ p ∈ P,
          (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) :=
      (tsum_eq_sum (s := T) htermzero).symm

private theorem finset_prod_le_prod_of_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  suffices h : ∀ s : Finset α, (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, 0 ≤ g i) →
      (∀ i ∈ s, f i ≤ g i) → ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i by
    exact h s hf hg hle
  intro s
  induction s using Finset.induction_on with
  | empty => intro hf hg hle; simp
  | @insert a s ha ih =>
      intro hf hg hle
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfA := hf a (Finset.mem_insert_self a s)
      have hgA := hg a (Finset.mem_insert_self a s)
      have hleA := hle a (Finset.mem_insert_self a s)
      have hfS : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hgS : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hleS : ∀ i ∈ s, f i ≤ g i := fun i hi => hle i (Finset.mem_insert_of_mem hi)
      have hprodF : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfS
      exact mul_le_mul hleA (ih hfS hgS hleS) hprodF hgA

private theorem harmonicProductLaw_primeVectorMass_le {k : ℕ} (W : ℕ)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, Nat.Coprime p W)
    (X : Fin k → ℕ) (hW : 0 < W) (hX : ∀ i, 0 < X i)
    (hXscale : ∀ i, 4 * W ≤ X i)
    (hlog : ∀ i, 4 * (W : ℝ) ≤ Real.log (X i : ℝ))
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W) (a : ℕ → ℕ) :
    (∑' σ : ℕ, harmonicProductLaw W X σ *
      (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)) ≤
      (6 : ℝ) ^ k * ∏ p ∈ P,
        (((a p + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ (a p)) := by
  classical
  let PrimeIndex := {p : ℕ // p ∈ P}
  letI : Fintype PrimeIndex := Finset.fintypeCoeSort P
  have hprodSubtypeReal (f : ℕ → ℝ) :
      (∏ p : PrimeIndex, f p.val) = ∏ p ∈ P, f p := by
    simpa [PrimeIndex] using
      (Finset.prod_subtype (p := fun x : ℕ => x ∈ P)
        (F := (inferInstance : Fintype PrimeIndex)) (s := P)
        (h := fun x : ℕ => Iff.rfl) (f := f)).symm
  have hprodSubtypeNat (f : ℕ → ℕ) :
      (∏ p : PrimeIndex, f p.val) = ∏ p ∈ P, f p := by
    simpa [PrimeIndex] using
      (Finset.prod_subtype (p := fun x : ℕ => x ∈ P)
        (F := (inferInstance : Fintype PrimeIndex)) (s := P)
        (h := fun x : ℕ => Iff.rfl) (f := f)).symm
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let weight : (Fin k → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (X i) W (t i)
  let rawMass : Fin k → (PrimeIndex → ℕ) → ℝ := fun i v =>
    ∑' n : ℕ, harmonicNatLaw (X i) W n *
      (if ∀ p : PrimeIndex, Nat.factorization n p.val = v p then 1 else 0)
  let rowVectors : Fin k → Finset (PrimeIndex → ℕ) := fun _ =>
    Fintype.piFinset (fun p : PrimeIndex => Finset.Iic (a p.val))
  let allAlloc : Finset (Fin k → PrimeIndex → ℕ) := Fintype.piFinset rowVectors
  let allocations := allAlloc.filter (fun v => ∀ p : PrimeIndex, ∑ i, v i p = a p.val)
  let allocOf (t : Fin k → ℕ) : Fin k → PrimeIndex → ℕ := fun i p =>
    Nat.factorization (t i) p.val
  let denominator (v : PrimeIndex → ℕ) : ℝ :=
    ∏ p : PrimeIndex, (p.val : ℝ) ^ (v p)
  have hweight_zero (t : Fin k → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 :=
      harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hLawNonneg (i : Fin k) (n : ℕ) : 0 ≤ harmonicNatLaw (X i) W n := by
    unfold harmonicNatLaw
    split_ifs with h
    · have hnpos : 0 < n := lt_of_lt_of_le (hX i) h.1
      positivity [hH i]
    · simp
  have hrawNonneg (i : Fin k) (v : PrimeIndex → ℕ) : 0 ≤ rawMass i v := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg (hLawNonneg i n) (by split_ifs <;> norm_num)
  have hrawSum (i : Fin k) (v : PrimeIndex → ℕ) :
      rawMass i v = ∑ n ∈ S i, harmonicNatLaw (X i) W n *
        (if ∀ p : PrimeIndex, Nat.factorization n p.val = v p then 1 else 0) := by
    have hzero (n : ℕ) (hn : n ∉ S i) :
        harmonicNatLaw (X i) W n *
          (if ∀ p : PrimeIndex, Nat.factorization n p.val = v p then 1 else 0) = 0 := by
      rw [harmonicNatLaw_zero_of_not_mem (X i) W n (by simpa [S] using hn)]
      simp
    unfold rawMass
    rw [tsum_eq_sum (s := S i) hzero]
  have hrawBound (i : Fin k) (v : PrimeIndex → ℕ) :
      rawMass i v ≤ 6 / denominator v := by
    let av : ℕ → ℕ := fun p => if hp : p ∈ P then v ⟨p, hp⟩ else 0
    have h := harmonicNatPrimeVectorMass_le (X i) W P hprime hcop hW
      (hXscale i) (hlog i) av
    have hcond (n : ℕ) : (∀ p ∈ P, Nat.factorization n p = av p) ↔
        (∀ p : PrimeIndex, Nat.factorization n p.val = v p) := by
      constructor
      · intro h p
        have hp := h p.val p.property
        simpa [av] using hp
      · intro h p hp
        have hp' := h ⟨p, hp⟩
        simpa [av, hp] using hp'
    have hav (p : PrimeIndex) : av p.val = v p := by simp [av, p.property]
    have hprodSubtype :
        (∏ p : PrimeIndex, (p.val : ℝ) ^ (v p)) =
          ∏ p ∈ P, (p : ℝ) ^ (av p) := by
      calc
        (∏ p : PrimeIndex, (p.val : ℝ) ^ (v p)) =
            ∏ p : PrimeIndex, (p.val : ℝ) ^ (av p.val) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [hav p]
        _ = ∏ p ∈ P, (p : ℝ) ^ (av p) :=
          hprodSubtypeReal (fun p => (p : ℝ) ^ (av p))
    have hden : denominator v = ∏ p ∈ P, (p : ℝ) ^ (av p) := by
      simpa [denominator] using hprodSubtype
    dsimp [rawMass]
    simpa only [hcond, denominator, hden] using h
  have hDenomProduct (v : Fin k → PrimeIndex → ℕ)
      (hv : v ∈ allocations) :
      (∏ i, denominator (v i)) = ∏ p ∈ P, (p : ℝ) ^ (a p) := by
    have hsum (p : PrimeIndex) : ∑ i, v i p = a p.val :=
      (Finset.mem_filter.mp hv).2 p
    have hprodSubtype := hprodSubtypeReal (fun p => (p : ℝ) ^ (a p))
    calc
      (∏ i, denominator (v i)) =
          ∏ p : PrimeIndex, ∏ i, (p.val : ℝ) ^ (v i p) := by
        simp only [denominator]
        exact Finset.prod_comm
      _ = ∏ p : PrimeIndex, (p.val : ℝ) ^ (∑ i, v i p) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Finset.prod_pow_eq_pow_sum]
      _ = ∏ p : PrimeIndex, (p.val : ℝ) ^ (a p.val) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [hsum p]
      _ = ∏ p ∈ P, (p : ℝ) ^ (a p) := hprodSubtype
  let rowEvent (i : Fin k) (n : ℕ) (v : PrimeIndex → ℕ) : ℝ :=
    if ∀ p : PrimeIndex, Nat.factorization n p.val = v p then 1 else 0
  let allocIndicator (t : Fin k → ℕ) (v : Fin k → PrimeIndex → ℕ) : ℝ :=
    ∏ i, rowEvent i (t i) (v i)
  have hallocNonneg (t : Fin k → ℕ) (v : Fin k → PrimeIndex → ℕ) :
      0 ≤ allocIndicator t v := by
    dsimp [allocIndicator]
    apply Finset.prod_nonneg
    intro i hi
    dsimp [rowEvent]
    split_ifs <;> norm_num
  have hpoint (t : Fin k → ℕ) (ht : t ∈ T) :
      (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) ≤
        ∑ v ∈ allocations, allocIndicator t v := by
    classical
    by_cases htotal : ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p
    · let v0 := allocOf t
      have hv0all : v0 ∈ allAlloc := by
        apply Fintype.mem_piFinset.mpr
        intro i
        apply Fintype.mem_piFinset.mpr
        intro p
        apply Finset.mem_Iic.mpr
        have hle : Nat.factorization (t i) p.val ≤
            ∑ j, Nat.factorization (t j) p.val :=
          Finset.single_le_sum
            (f := fun j => Nat.factorization (t j) p.val)
            (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
        rw [htotal p.val p.property] at hle
        simpa [allocOf] using hle
      have hv0sum : ∀ p : PrimeIndex, ∑ i, v0 i p = a p.val := by
        intro p
        simpa [v0, allocOf] using htotal p.val p.property
      have hv0 : v0 ∈ allocations := Finset.mem_filter.mpr ⟨hv0all, hv0sum⟩
      have hsingle := Finset.single_le_sum
        (f := fun v => allocIndicator t v)
        (fun v hv => hallocNonneg t v) hv0
      have hvalue : allocIndicator t v0 = 1 := by
        simp [allocIndicator, rowEvent, v0, allocOf]
      rw [hvalue] at hsingle
      calc
        (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) = 1 :=
          if_pos htotal
        _ ≤ ∑ v ∈ allocations, allocIndicator t v := hsingle
    · simp only [if_neg htotal]
      apply Finset.sum_nonneg
      intro v hv
      exact hallocNonneg t v
  have hrawPush (v : Fin k → PrimeIndex → ℕ) :
      (∑ t ∈ T, weight t * allocIndicator t v) = ∏ i, rawMass i (v i) := by
    calc
      (∑ t ∈ T, weight t * allocIndicator t v) =
          ∑ t ∈ T, ∏ i, (harmonicNatLaw (X i) W (t i) * rowEvent i (t i) (v i)) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [weight, allocIndicator, rowEvent]
        rw [← Finset.prod_mul_distrib]
      _ = ∏ i, ∑ n ∈ S i,
          harmonicNatLaw (X i) W n * rowEvent i n (v i) := by
        simpa [T] using (Finset.prod_univ_sum S
          (fun i n => harmonicNatLaw (X i) W n * rowEvent i n (v i))).symm
      _ = ∏ i, rawMass i (v i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← hrawSum i (v i)]
  have hmass := harmonicProductLaw_primeVectorMass_eq W P a X hX hH
  let lhs : ℝ := ∑' σ : ℕ, harmonicProductLaw W X σ *
    (if ∀ p ∈ P, Nat.factorization σ p = a p then 1 else 0)
  let Kden : ℝ := ∏ p ∈ P, (p : ℝ) ^ (a p)
  have hmassFinite : lhs =
      ∑ t ∈ T, weight t *
        (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := by
    dsimp [lhs]
    rw [hmass]
    have hzero (t : Fin k → ℕ) (ht : t ∉ T) :
        weight t * (if ∀ p ∈ P,
          (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) = 0 := by
      simp [weight, hweight_zero t ht]
    rw [tsum_eq_sum (s := T) hzero]
  have hsumUpper :
      (∑ t ∈ T, weight t *
        (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0)) ≤
        ∑ v ∈ allocations, ∏ i, rawMass i (v i) := by
    calc
      _ ≤ ∑ t ∈ T, weight t * (∑ v ∈ allocations, allocIndicator t v) := by
        apply Finset.sum_le_sum
        intro t ht
        have hwt : 0 ≤ weight t := by
          dsimp [weight]
          apply Finset.prod_nonneg
          intro i hi
          exact hLawNonneg i (t i)
        exact mul_le_mul_of_nonneg_left (hpoint t ht) hwt
      _ = ∑ t ∈ T, ∑ v ∈ allocations, weight t * allocIndicator t v := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
      _ = ∑ v ∈ allocations, ∑ t ∈ T, weight t * allocIndicator t v := by
        rw [Finset.sum_comm]
      _ = ∑ v ∈ allocations, ∏ i, rawMass i (v i) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hrawPush v
  have hcardAll : allAlloc.card =
      ∏ p : PrimeIndex, (a p.val + 1) ^ k := by
    calc
      allAlloc.card = ∏ i, (rowVectors i).card := by simp [allAlloc]
      _ = ∏ i, ∏ p : PrimeIndex, (a p.val + 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [rowVectors, Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro p hp
        simp
      _ = ∏ p : PrimeIndex, ∏ i, (a p.val + 1) := by rw [Finset.prod_comm]
      _ = ∏ p : PrimeIndex, (a p.val + 1) ^ k := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [Finset.prod_const, Fintype.card_fin]
  have hprodSubtype := hprodSubtypeNat (fun p => (a p + 1) ^ k)
  have hcard : allocations.card ≤ ∏ p ∈ P, (a p + 1) ^ k := by
    calc
      allocations.card ≤ allAlloc.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ∏ p ∈ P, (a p + 1) ^ k := by rw [hcardAll, hprodSubtype]
  have hcardReal : (allocations.card : ℝ) ≤
      ∏ p ∈ P, ((a p + 1 : ℕ) : ℝ) ^ k := by exact_mod_cast hcard
  have hKdenPos : 0 < Kden := by
    dsimp [Kden]
    apply Finset.prod_pos
    intro p hp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
    exact pow_pos hpR _
  have hbaseBound : 0 ≤ (6 : ℝ) ^ k / Kden :=
    div_nonneg (by positivity) hKdenPos.le
  have hallocBound :
      (∑ v ∈ allocations, ∏ i, rawMass i (v i)) ≤
        (6 : ℝ) ^ k / Kden * allocations.card := by
    calc
      _ ≤ ∑ v ∈ allocations, (6 : ℝ) ^ k / Kden := by
        apply Finset.sum_le_sum
        intro v hv
        have hrowBound :
            ∏ i, rawMass i (v i) ≤ ∏ i, (6 : ℝ) / denominator (v i) := by
          exact finset_prod_le_prod_of_nonneg Finset.univ
            (fun i => rawMass i (v i)) (fun i => (6 : ℝ) / denominator (v i))
            (by intro i hi; exact hrawNonneg i (v i))
            (by intro i hi; positivity)
            (by intro i hi; exact hrawBound i (v i))
        have hden := hDenomProduct v hv
        calc
          ∏ i, rawMass i (v i) ≤ ∏ i, (6 : ℝ) / denominator (v i) := hrowBound
          _ = (6 : ℝ) ^ k / Kden := by
            rw [Finset.prod_div_distrib]
            simp [Kden, denominator, Finset.prod_const, Fintype.card_fin, hden]
      _ = (6 : ℝ) ^ k / Kden * allocations.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hfinal :
      (6 : ℝ) ^ k / Kden * allocations.card ≤
        (6 : ℝ) ^ k * ∏ p ∈ P,
          (((a p + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ (a p)) := by
    have hnum : (allocations.card : ℝ) ≤
        ∏ p ∈ P, ((a p + 1 : ℕ) : ℝ) ^ k := hcardReal
    have hdenPos : 0 < Kden := hKdenPos
    calc
      (6 : ℝ) ^ k / Kden * allocations.card ≤
          (6 : ℝ) ^ k / Kden * ∏ p ∈ P, ((a p + 1 : ℕ) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = (6 : ℝ) ^ k * ∏ p ∈ P,
          (((a p + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ (a p)) := by
        rw [Finset.prod_div_distrib]
        change (6 : ℝ) ^ k / Kden *
            (∏ p ∈ P, ((a p + 1 : ℕ) : ℝ) ^ k) =
          (6 : ℝ) ^ k *
            ((∏ p ∈ P, ((a p + 1 : ℕ) : ℝ) ^ k) / Kden)
        field_simp [ne_of_gt hdenPos]
  calc
    lhs = ∑ t ∈ T, weight t *
        (if ∀ p ∈ P, (∑ i, Nat.factorization (t i) p) = a p then 1 else 0) := hmassFinite
    _ ≤ ∑ v ∈ allocations, ∏ i, rawMass i (v i) := hsumUpper
    _ ≤ (6 : ℝ) ^ k / Kden * allocations.card := hallocBound
    _ ≤ (6 : ℝ) ^ k * ∏ p ∈ P,
        (((a p + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ (a p)) := hfinal

private theorem harmonicProductLaw_valuationMass_le {k : ℕ} (W p a : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W)
    (hpowCop : ∀ r, Nat.Coprime (p ^ r) W)
    (hraw : ∀ i r, Nat.Coprime (p ^ r) W →
      primeValuationMass (fun n => harmonicNatLaw (X i) W n) p r ≤
        6 / (p : ℝ) ^ r) :
    primeValuationMass (harmonicProductLaw W X) p a ≤
      (6 : ℝ) ^ k * (((a + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ a := by
  classical
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let weight (t : Fin k → ℕ) : ℝ := ∏ i, harmonicNatLaw (X i) W (t i)
  let val (t : Fin k → ℕ) : Fin k → ℕ := fun i => Nat.factorization (t i) p
  let good : Finset (Fin k → ℕ) := T.filter (fun t => (∑ i, val t i) = a)
  let V₀ : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k => Finset.range (a + 1))
  let V : Finset (Fin k → ℕ) := V₀.filter (fun v => (∑ i, v i) = a)
  have hμnonneg (i : Fin k) (n : ℕ) : 0 ≤ harmonicNatLaw (X i) W n := by
    unfold harmonicNatLaw
    split_ifs with h
    · have hn : 0 < n := lt_of_lt_of_le (hX i) h.1
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      positivity [hH i]
    · simp
  have hrawNonneg (i : Fin k) (r : ℕ) :
      0 ≤ primeValuationMass (fun n => harmonicNatLaw (X i) W n) p r := by
    unfold primeValuationMass
    apply tsum_nonneg
    intro n
    exact mul_nonneg (hμnonneg i n) (by split_ifs <;> norm_num)
  have htermzero (t : Fin k → ℕ) (ht : t ∉ T) :
      weight t * (if (∑ i, val t i) = a then 1 else 0) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (X i) W (t i) = 0 := by
      exact harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    have hwt : weight t = 0 := by
      dsimp [weight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
    rw [hwt]
    simp
  have hmassTsum := harmonicProductLaw_primeValuationMass_eq W p a X hX hH
  have hmassFinite :
      primeValuationMass (harmonicProductLaw W X) p a =
        ∑ t ∈ good, weight t := by
    rw [hmassTsum, tsum_eq_sum (s := T) htermzero]
    dsimp [good]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hval : (∑ i, val t i) = a <;> simp [hval]
  have hMaps : Set.MapsTo val (↑good : Set (Fin k → ℕ)) (↑V : Set (Fin k → ℕ)) := by
    intro t ht
    have hgt : t ∈ good := ht
    have hsum : (∑ i, val t i) = a := (Finset.mem_filter.mp hgt).2
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      apply Finset.mem_range.mpr
      have hle : val t i ≤ ∑ j, val t j := by
        exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · exact hsum
  have hfiberwise :
      (∑ t ∈ good, weight t) =
        ∑ v ∈ V, ∑ t ∈ good with val t = v, weight t := by
    exact (Finset.sum_fiberwise_of_maps_to hMaps weight).symm
  have hRawEq (i : Fin k) (r : ℕ) :
      primeValuationMass (fun n => harmonicNatLaw (X i) W n) p r =
        ∑ n ∈ (S i).filter (fun n => Nat.factorization n p = r),
          harmonicNatLaw (X i) W n := by
    have hzero (n : ℕ) (hn : n ∉ S i) :
        harmonicNatLaw (X i) W n * (if Nat.factorization n p = r then 1 else 0) = 0 := by
      rw [harmonicNatLaw_zero_of_not_mem (X i) W n (by simpa [S] using hn)]
      simp
    unfold primeValuationMass
    rw [tsum_eq_sum (s := S i) hzero]
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hv : Nat.factorization n p = r <;> simp [hv]
  have hFiberSet (v : Fin k → ℕ) (hv : v ∈ V) :
      good.filter (fun t => val t = v) =
        Fintype.piFinset (fun i => (S i).filter (fun n => Nat.factorization n p = v i)) := by
    have hsumV : (∑ i, v i) = a := (Finset.mem_filter.mp hv).2
    ext t
    constructor
    · intro ht
      have hparts := Finset.mem_filter.mp ht
      have hgood := Finset.mem_filter.mp hparts.1
      have htT : t ∈ T := hgood.1
      have hvalEq : val t = v := hparts.2
      apply Fintype.mem_piFinset.mpr
      intro i
      have hiS : t i ∈ S i := Fintype.mem_piFinset.mp htT i
      have hvi : val t i = v i := congrFun hvalEq i
      exact Finset.mem_filter.mpr ⟨hiS, by simpa [val] using hvi⟩
    · intro ht
      have htPi := Fintype.mem_piFinset.mp ht
      have hvalEq : val t = v := by
        funext i
        exact (Finset.mem_filter.mp (htPi i)).2
      have htT : t ∈ T := Fintype.mem_piFinset.mpr fun i =>
        (Finset.mem_filter.mp (htPi i)).1
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨htT, by simpa [hvalEq] using hsumV⟩
      · exact hvalEq
  have hFiberSum (v : Fin k → ℕ) (hv : v ∈ V) :
      (∑ t ∈ good with val t = v, weight t) =
        ∏ i, primeValuationMass (fun n => harmonicNatLaw (X i) W n) p (v i) := by
    let Sv : Fin k → Finset ℕ := fun i =>
      (S i).filter (fun n => Nat.factorization n p = v i)
    rw [show good.filter (fun t => val t = v) =
      Fintype.piFinset Sv by simpa [Sv] using hFiberSet v hv]
    calc
      (∑ t ∈ Fintype.piFinset Sv, weight t) =
          ∏ i, ∑ n ∈ Sv i, harmonicNatLaw (X i) W n := by
        simpa [weight] using
          (Finset.prod_univ_sum Sv (fun i n => harmonicNatLaw (X i) W n)).symm
      _ = ∏ i, primeValuationMass (fun n => harmonicNatLaw (X i) W n) p (v i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (hRawEq i (v i)).symm
  have hprodBound (v : Fin k → ℕ) (hv : v ∈ V) :
      ∏ i, primeValuationMass (fun n => harmonicNatLaw (X i) W n) p (v i) ≤
        (6 : ℝ) ^ k / (p : ℝ) ^ a := by
    have hsumv : (∑ i, v i) = a := (Finset.mem_filter.mp hv).2
    have hprodRaw :
        ∏ i, primeValuationMass (fun n => harmonicNatLaw (X i) W n) p (v i) ≤
          ∏ i, (6 / (p : ℝ) ^ (v i)) := by
      apply finset_prod_le_prod_of_nonneg
      · intro i hi
        exact hrawNonneg i (v i)
      · intro i hi
        positivity
      · intro i hi
        exact hraw i (v i) (hpowCop (v i))
    calc
      _ ≤ ∏ i, (6 / (p : ℝ) ^ (v i)) := hprodRaw
      _ = (6 : ℝ) ^ k / (p : ℝ) ^ a := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Finset.prod_pow_eq_pow_sum, hsumv]
  have hcardV0 : V₀.card = (a + 1) ^ k := by
    simp [V₀, Fintype.card_piFinset_const]
  have hcardV : V.card ≤ (a + 1) ^ k := by
    calc
      V.card ≤ V₀.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = (a + 1) ^ k := hcardV0
  have hCnonneg : 0 ≤ (6 : ℝ) ^ k / (p : ℝ) ^ a := by positivity
  calc
    primeValuationMass (harmonicProductLaw W X) p a = ∑ t ∈ good, weight t := hmassFinite
    _ = ∑ v ∈ V, ∑ t ∈ good with val t = v, weight t := hfiberwise
    _ = ∑ v ∈ V,
        ∏ i, primeValuationMass (fun n => harmonicNatLaw (X i) W n) p (v i) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hFiberSum v hv
    _ ≤ ∑ _v ∈ V, (6 : ℝ) ^ k / (p : ℝ) ^ a :=
      Finset.sum_le_sum fun v hv => hprodBound v hv
    _ = (V.card : ℝ) * ((6 : ℝ) ^ k / (p : ℝ) ^ a) := by simp [Finset.sum_const]
    _ ≤ ((a + 1 : ℕ) : ℝ) ^ k * ((6 : ℝ) ^ k / (p : ℝ) ^ a) := by
      gcongr
      exact_mod_cast hcardV
    _ = (6 : ℝ) ^ k * ((a + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ a := by ring

/-- Joint Euler-product domination for the q fresh divisor draws: each row has at most b raw
factors and contributes valuation mass bounded by a polynomial times p⁻ᵃ; a single global
constant raised to bq dominates the whole product (§3 lines 581–618). -/
theorem harmonic_divisor_valuation_domination {n q b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (D : Fin q → DivisorTemplate n b) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ N in atTop, ∀ p, p.Prime → ∀ a : Fin q → ℕ,
      (∏ u, primeValuationMass
        (divisorTemplateLaw A N (D u)) p (a u)) ≤
      C₀ ^ (b * q) * ∏ u,
        ((a u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a u) := by
  refine ⟨6, by norm_num, ?_⟩
  have hscale : ∀ᶠ N in atTop, ∀ i : Fin n,
      4 * primorial (N + 1) ≤ A.X N i ∧
      4 * (primorial (N + 1) : ℝ) ≤ Real.log (A.X N i : ℝ) := by
    simp only [Filter.eventually_all]
    intro i
    have hratio : ∀ᶠ N in atTop,
        (4 : ℝ) ≤ Real.log (A.X N i : ℝ) / (A.H N i : ℝ) := by
      simpa using
        (A.Xdom i 1 (by norm_num : (0 : ℝ) < 1)).eventually_ge_atTop (4 : ℝ)
    filter_upwards [(A.eventual_X i), hratio] with N hX hratio
    have hMleH : A.M N ≤ A.H N i :=
      Nat.le_of_dvd (A.Hpos N i) (A.Hdiv N i)
    have hWleH : primorial (N + 1) ≤ A.H N i := (A.Wle N).trans hMleH
    have hHposR : 0 < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
    have hWleHR : (primorial (N + 1) : ℝ) ≤ (A.H N i : ℝ) := by
      exact_mod_cast hWleH
    have hlogH : 4 * (A.H N i : ℝ) ≤ Real.log (A.X N i : ℝ) :=
      (le_div_iff₀ hHposR).mp hratio
    exact ⟨hX, (mul_le_mul_of_nonneg_left hWleHR (by norm_num)).trans hlogH⟩
  filter_upwards [hscale] with N hscaleN
  intro p hp a
  let W : ℕ := primorial (N + 1)
  have hWpos : 0 < W := by dsimp [W]; exact primorial_pos _
  have hscaleX (i : Fin n) : 4 * W ≤ A.X N i := by
    simpa [W] using (hscaleN i).1
  have hscaleLog (i : Fin n) :
      4 * (W : ℝ) ≤ Real.log (A.X N i : ℝ) := by
    simpa [W] using (hscaleN i).2
  by_cases hpSmall : p ≤ N + 1
  · have hpW : p ∣ W := by
      dsimp [W]
      exact hp.dvd_primorial_iff.mpr hpSmall
    have hlocal (u : Fin q) :
        primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) =
          if a u = 0 then 1 else 0 := by
      let Xraw : Fin (D u).arity → ℕ := fun j => A.X N ((D u).cutoff j)
      have hXraw (j : Fin (D u).arity) : 0 < Xraw j :=
        A.Xpos N ((D u).cutoff j)
      have hHraw (j : Fin (D u).arity) :
          0 < harmonicNormalizer (Xraw j) W :=
        harmonicNormalizer_pos_of_cutoff (Xraw j) W hWpos (hscaleX ((D u).cutoff j))
      change primeValuationMass (harmonicProductLaw W Xraw) p (a u) = _
      exact harmonicProductLaw_primeValuationMass W p hp hpW Xraw hXraw hHraw (a u)
    by_cases hAzero : ∀ u, a u = 0
    · have hprod :
          (∏ u, primeValuationMass (divisorTemplateLaw A N (D u)) p (a u)) = 1 := by
        simp_rw [hlocal]
        simp [hAzero]
      rw [hprod]
      simp [hAzero]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 6)
    · obtain ⟨u, hu⟩ := not_forall.mp hAzero
      have hzero :
          primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) = 0 := by
        rw [hlocal u]
        simp [hu]
      rw [Finset.prod_eq_zero (Finset.mem_univ u) hzero]
      positivity
  · have hpNotW : ¬ p ∣ W := by
      intro hdiv
      have hpLe : p ≤ N + 1 := by
        apply hp.dvd_primorial_iff.mp
        simpa [W] using hdiv
      omega
    have hcopP : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpNotW
    have hpowCop : ∀ r, Nat.Coprime (p ^ r) W := by
      intro r
      by_cases hr : r = 0
      · simp [hr]
      · exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hr) p W).2 hcopP
    have hlocalBound (u : Fin q) :
        primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) ≤
          (6 : ℝ) ^ (D u).arity *
            (((a u + 1 : ℕ) : ℝ) ^ (D u).arity) / (p : ℝ) ^ (a u) := by
      let Xraw : Fin (D u).arity → ℕ := fun j => A.X N ((D u).cutoff j)
      have hXraw (j : Fin (D u).arity) : 0 < Xraw j :=
        A.Xpos N ((D u).cutoff j)
      have hHraw (j : Fin (D u).arity) :
          0 < harmonicNormalizer (Xraw j) W :=
        harmonicNormalizer_pos_of_cutoff (Xraw j) W hWpos (hscaleX ((D u).cutoff j))
      change primeValuationMass (harmonicProductLaw W Xraw) p (a u) ≤ _
      exact harmonicProductLaw_valuationMass_le W p (a u) Xraw hXraw hHraw hpowCop
        (by
          intro j r hcop
          exact harmonicNatValuationMass_le (Xraw j) W p r hWpos
            (hscaleX ((D u).cutoff j)) (hscaleLog ((D u).cutoff j)) hp hcop)
    have hlocalTight (u : Fin q) :
        primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) ≤
          (6 : ℝ) ^ b *
            ((((a u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (a u)) := by
      have hArity := (D u).arity_le
      let B : ℝ := ((a u + 1 : ℕ) : ℝ)
      have hB : 1 ≤ B := by
        dsimp [B]
        exact_mod_cast (show 1 ≤ a u + 1 by omega)
      have hnum :
          (6 : ℝ) ^ (D u).arity * B ^ (D u).arity ≤ (6 : ℝ) ^ b * B ^ b := by
        exact mul_le_mul
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) hArity)
          (pow_le_pow_right₀ hB hArity)
          (by positivity) (by positivity)
      have hden : 0 ≤ (p : ℝ) ^ (a u) := by positivity
      have hbound := div_le_div_of_nonneg_right hnum hden
      calc
        primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) ≤
            (6 : ℝ) ^ (D u).arity * B ^ (D u).arity / (p : ℝ) ^ (a u) := by
          simpa [B] using hlocalBound u
        _ ≤ (6 : ℝ) ^ b * B ^ b / (p : ℝ) ^ (a u) := hbound
        _ = (6 : ℝ) ^ b * (B ^ b / (p : ℝ) ^ (a u)) := by ring
    have hLawNonneg (u : Fin q) (σ : ℕ) :
        0 ≤ divisorTemplateLaw A N (D u) σ := by
      let Xraw : Fin (D u).arity → ℕ := fun j => A.X N ((D u).cutoff j)
      have hXraw (j : Fin (D u).arity) : 0 < Xraw j :=
        A.Xpos N ((D u).cutoff j)
      have hHraw (j : Fin (D u).arity) :
          0 < harmonicNormalizer (Xraw j) W :=
        harmonicNormalizer_pos_of_cutoff (Xraw j) W hWpos (hscaleX ((D u).cutoff j))
      have hμ (j : Fin (D u).arity) (z : ℕ) :
          0 ≤ harmonicNatLaw (Xraw j) W z := by
        unfold harmonicNatLaw
        split_ifs with hz
        · have hzpos : 0 < z := lt_of_lt_of_le (hXraw j) hz.1
          positivity [hHraw j]
        · simp
      change 0 ≤ harmonicProductLaw W Xraw σ
      unfold harmonicProductLaw
      apply tsum_nonneg
      intro t
      by_cases hprod : ∏ j, t j = σ
      · simp [hprod]
        exact Finset.prod_nonneg fun j _ => hμ j (t j)
      · simp [hprod]
    have hMassNonneg (u : Fin q) :
        0 ≤ primeValuationMass (divisorTemplateLaw A N (D u)) p (a u) := by
      unfold primeValuationMass
      apply tsum_nonneg
      intro σ
      exact mul_nonneg (hLawNonneg u σ) (by split_ifs <;> norm_num)
    have hprodBound :
        (∏ u, primeValuationMass (divisorTemplateLaw A N (D u)) p (a u)) ≤
          ∏ u, ((6 : ℝ) ^ b *
            ((((a u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (a u))) := by
      exact finset_prod_le_prod_of_nonneg Finset.univ
        (fun u => primeValuationMass (divisorTemplateLaw A N (D u)) p (a u))
        (fun u => (6 : ℝ) ^ b *
          ((((a u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (a u)))
        (by intro u hu; exact hMassNonneg u)
        (by intro u hu; positivity)
        (by intro u hu; exact hlocalTight u)
    calc
      (∏ u, primeValuationMass (divisorTemplateLaw A N (D u)) p (a u)) ≤
          ∏ u, ((6 : ℝ) ^ b *
            ((((a u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (a u))) := hprodBound
      _ = (6 : ℝ) ^ (b * q) *
          ∏ u, (((a u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (a u) := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const, pow_mul, Fintype.card_fin]

/-- The two geometric valuation series from regular and exceptional local tests. -/
def regularDivisorExcessSeries (p q b : ℕ) : ℝ :=
  ∑' A : ℕ, ∑' B : ℕ,
    if 1 ≤ B ∧ B ≤ A then
      (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ (b * q) /
        (p : ℝ) ^ (A + B)
    else 0

/-- The valuation series when a polynomial test is exceptional modulo p. -/
def exceptionalDivisorExcessSeries (p q b : ℕ) : ℝ :=
  ∑' A : ℕ, if 1 ≤ A then
    (((A + 1 : ℕ) : ℝ) ^ (b * q)) / (p : ℝ) ^ A else 0

private def expPolyWeight (k n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ n

private theorem expPolyWeight_summable (k : ℕ) :
    Summable (fun n : ℕ => expPolyWeight k n) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  have htail : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ k * (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hmul := htail.mul_left (2 : ℝ)
  exact hmul.congr fun n => by
    simp only [expPolyWeight]
    rw [pow_succ]
    field_simp

private theorem regularExpTerm_bound (p k A B : ℕ) (hp : p.Prime) :
    (if 1 ≤ B ∧ B ≤ A then
      (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k / (p : ℝ) ^ (A + B) else 0) ≤
    (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hAB : 1 ≤ B ∧ B ≤ A
  · have hsum0 : 2 ≤ A + B := by omega
    let t := A + B - 2
    have hsum : 2 + t = A + B := by dsimp [t]; omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ t ≤ (p : ℝ) ^ (A + B) := by
      rw [← hsum, pow_add]
      gcongr
    have hrecip : 1 / (p : ℝ) ^ (A + B) ≤
        1 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ t) :=
      one_div_le_one_div_of_le (by positivity) hden
    have htwo : (2 : ℝ) ^ (A + B) = 4 * (2 : ℝ) ^ t := by
      rw [← hsum, pow_add]
      norm_num
    have hfactor :
        (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B =
          ((((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ)) ^ k) /
            ((p : ℝ) ^ 2 * (2 : ℝ) ^ t) := by
      unfold expPolyWeight
      calc
        _ = (4 / (p : ℝ) ^ 2) *
            ((((A + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ)) ^ k *
              (1 / 2 : ℝ) ^ (A + B)) := by
                calc
                  _ = (4 / (p : ℝ) ^ 2) *
                      ((((A + 1 : ℕ) : ℝ) ^ k * ((B + 1 : ℕ) : ℝ) ^ k) *
                        ((1 / 2 : ℝ) ^ A * (1 / 2 : ℝ) ^ B)) := by ring
                  _ = _ := by rw [← mul_pow, ← pow_add]
        _ = _ := by rw [one_div_pow, htwo]; field_simp [ne_of_gt hp0]
    simp only [if_pos hAB]
    calc
      ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) / (p : ℝ) ^ (A + B) =
          ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) *
            (1 / (p : ℝ) ^ (A + B)) := by ring
      _ ≤ ((((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ k) *
            (1 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ t)) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (4 / (p : ℝ) ^ 2) * expPolyWeight k A * expPolyWeight k B := by
        simpa only [div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using hfactor.symm
  · simp [hAB]
    unfold expPolyWeight
    positivity

private theorem exceptionalExpTerm_bound (p k A : ℕ) (hp : p.Prime) :
    (if 1 ≤ A then (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A else 0) ≤
      (2 / (p : ℝ)) * expPolyWeight k A := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hA : 1 ≤ A
  · let t := A - 1
    have hsum : 1 + t = A := by dsimp [t]; omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hden : (p : ℝ) * (2 : ℝ) ^ t ≤ (p : ℝ) ^ A := by
      rw [← hsum, pow_add, pow_one]
      gcongr
    have hrecip : 1 / (p : ℝ) ^ A ≤ 1 / ((p : ℝ) * (2 : ℝ) ^ t) :=
      one_div_le_one_div_of_le (by positivity) hden
    have htwo : (2 : ℝ) ^ A = 2 * (2 : ℝ) ^ t := by
      rw [← hsum, pow_add]
      norm_num
    have hfactor :
        (2 / (p : ℝ)) * expPolyWeight k A =
          (((A + 1 : ℕ) : ℝ) ^ k) / ((p : ℝ) * (2 : ℝ) ^ t) := by
      unfold expPolyWeight
      rw [one_div_pow, htwo]
      field_simp [ne_of_gt hp0]
    simp only [if_pos hA]
    calc
      (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A =
          (((A + 1 : ℕ) : ℝ) ^ k) * (1 / (p : ℝ) ^ A) := by ring
      _ ≤ (((A + 1 : ℕ) : ℝ) ^ k) * (1 / ((p : ℝ) * (2 : ℝ) ^ t)) :=
          mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (2 / (p : ℝ)) * expPolyWeight k A := by
        simpa only [div_eq_mul_inv, one_mul] using hfactor.symm
  · simp [hA]
    unfold expPolyWeight
    positivity

/-- Both local valuation series are `O(p⁻²)`: the exceptional series gains its extra
`1/p` from the polynomial-root test (§3 lines 620–648). -/
theorem local_divisor_excess_prime_square_bound (q b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      regularDivisorExcessSeries p q b ≤ C / (p : ℝ) ^ 2 ∧
      exceptionalDivisorExcessSeries p q b / p ≤ C / (p : ℝ) ^ 2 := by
  let k := b * q
  let F : ℝ := ∑' A : ℕ, expPolyWeight k A
  let G : ℝ := ∑' x : ℕ × ℕ, expPolyWeight k x.1 * expPolyWeight k x.2
  let C : ℝ := 4 * G + 2 * F + 1
  have hFsum : Summable (fun A : ℕ => expPolyWeight k A) := expPolyWeight_summable k
  have hFterm : ∀ A, 0 ≤ expPolyWeight k A := by
    intro A
    unfold expPolyWeight
    positivity
  have hFnonneg : 0 ≤ F := by
    dsimp [F]
    exact tsum_nonneg hFterm
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact tsum_nonneg fun x => mul_nonneg (hFterm x.1) (hFterm x.2)
  have hpair : Summable (fun x : ℕ × ℕ => expPolyWeight k x.1 * expPolyWeight k x.2) :=
    hFsum.mul_of_nonneg hFsum hFterm hFterm
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpDen : 0 < (p : ℝ) ^ 2 := by positivity
  let rterm : ℕ × ℕ → ℝ := fun x =>
    if 1 ≤ x.2 ∧ x.2 ≤ x.1 then
      (((x.1 + 1 : ℕ) : ℝ) * (x.2 + 1 : ℝ)) ^ k / (p : ℝ) ^ (x.1 + x.2)
    else 0
  let rcomp : ℕ × ℕ → ℝ := fun x =>
    (4 / (p : ℝ) ^ 2) * expPolyWeight k x.1 * expPolyWeight k x.2
  have hrterm_nonneg : ∀ x, 0 ≤ rterm x := by
    intro x
    dsimp [rterm]
    split_ifs <;> positivity
  have hrcomp_sum : Summable rcomp := by
    simpa [rcomp, mul_assoc] using hpair.mul_left (4 / (p : ℝ) ^ 2)
  have hrterm_le : ∀ x, rterm x ≤ rcomp x := by
    intro x
    dsimp [rterm, rcomp]
    exact regularExpTerm_bound p k x.1 x.2 hp
  have hrterm_sum : Summable rterm := hrcomp_sum.of_nonneg_of_le hrterm_nonneg hrterm_le
  have hrseries : regularDivisorExcessSeries p q b = ∑' x : ℕ × ℕ, rterm x := by
    simpa [regularDivisorExcessSeries, rterm, k] using hrterm_sum.tsum_prod.symm
  have hrbound : regularDivisorExcessSeries p q b ≤ (4 / (p : ℝ) ^ 2) * G := by
    calc
      regularDivisorExcessSeries p q b = ∑' x : ℕ × ℕ, rterm x := hrseries
      _ ≤ ∑' x : ℕ × ℕ, rcomp x :=
        Summable.tsum_le_tsum hrterm_le hrterm_sum hrcomp_sum
      _ = (4 / (p : ℝ) ^ 2) * G := by
        simpa [rcomp, G, mul_assoc] using hpair.tsum_mul_left (4 / (p : ℝ) ^ 2)
  have hCreg : 4 * G ≤ C := by
    dsimp [C]
    linarith [hFnonneg]
  have hRfinal : regularDivisorExcessSeries p q b ≤ C / (p : ℝ) ^ 2 := by
    calc
      regularDivisorExcessSeries p q b ≤ (4 / (p : ℝ) ^ 2) * G := hrbound
      _ = (4 * G) / (p : ℝ) ^ 2 := by ring
      _ ≤ C / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right hCreg hpDen.le
  let eterm : ℕ → ℝ := fun A =>
    if 1 ≤ A then (((A + 1 : ℕ) : ℝ) ^ k) / (p : ℝ) ^ A else 0
  let ecomp : ℕ → ℝ := fun A => (2 / (p : ℝ)) * expPolyWeight k A
  have heterm_nonneg : ∀ A, 0 ≤ eterm A := by
    intro A
    dsimp [eterm]
    split_ifs <;> positivity
  have hecomp_sum : Summable ecomp := by
    simpa [ecomp] using hFsum.mul_left (2 / (p : ℝ))
  have heterm_le : ∀ A, eterm A ≤ ecomp A := by
    intro A
    dsimp [eterm, ecomp]
    exact exceptionalExpTerm_bound p k A hp
  have heterm_sum : Summable eterm := hecomp_sum.of_nonneg_of_le heterm_nonneg heterm_le
  have heseries : exceptionalDivisorExcessSeries p q b = ∑' A : ℕ, eterm A := by
    simp [exceptionalDivisorExcessSeries, eterm, k, Nat.cast_add]
  have hebound : exceptionalDivisorExcessSeries p q b ≤ (2 / (p : ℝ)) * F := by
    calc
      exceptionalDivisorExcessSeries p q b = ∑' A : ℕ, eterm A := heseries
      _ ≤ ∑' A : ℕ, ecomp A := Summable.tsum_le_tsum heterm_le heterm_sum hecomp_sum
      _ = (2 / (p : ℝ)) * F := by
        simpa [ecomp, F] using hFsum.tsum_mul_left (2 / (p : ℝ))
  have hCexc : 2 * F ≤ C := by
    dsimp [C]
    linarith [hGnonneg]
  have hEfinal : exceptionalDivisorExcessSeries p q b / p ≤ C / (p : ℝ) ^ 2 := by
    calc
      exceptionalDivisorExcessSeries p q b / p ≤ ((2 / (p : ℝ)) * F) / p :=
        div_le_div_of_nonneg_right hebound hp0.le
      _ = (2 * F) / (p : ℝ) ^ 2 := by field_simp [ne_of_gt hp0]
      _ ≤ C / (p : ℝ) ^ 2 := div_le_div_of_nonneg_right hCexc hpDen.le
  exact ⟨hRfinal, hEfinal⟩

private theorem finiteL1_expectation_bound {α : Type*} [Fintype α]
    (μ ν f : α → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) :
    |(∑ x, μ x * f x) - ∑ x, ν x * f x| ≤ B * finiteL1 μ ν := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (μ x * f x - ν x * f x)| ≤
        ∑ x, |μ x * f x - ν x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |μ x - ν x| * B := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg (μ x - ν x))
    _ = B * finiteL1 μ ν := by
      rw [finiteL1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [mul_comm B]

private theorem tsum_pushforward_expectation {α β : Type*}
    [Fintype α] [DecidableEq α] (μ : β → ℝ) (ρ : β → α)
    (hμ : Summable μ) (f : α → ℝ) :
    (∑' x, μ x * f (ρ x)) =
      ∑ a, (∑' x, μ x * (if ρ x = a then 1 else 0)) * f a := by
  classical
  let g (a : α) (x : β) : ℝ := μ x * (if ρ x = a then 1 else 0)
  have hg (a : α) : Summable (g a) := by
    apply hμ.norm.of_norm_bounded
    intro x
    by_cases h : ρ x = a <;> simp [g, h]
  have hgf (a : α) : Summable (fun x => g a x * f a) := (hg a).mul_right (f a)
  have hcollapse (x : β) : (∑ a, g a x * f a) = μ x * f (ρ x) := by
    calc
      (∑ a, g a x * f a) = μ x * ∑ a, (if ρ x = a then f a else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : ρ x = a <;> simp [g, h]
      _ = μ x * f (ρ x) := by simp [Finset.sum_ite_eq', eq_comm]
  calc
    (∑' x, μ x * f (ρ x)) = ∑' x, ∑ a, g a x * f a := by
      apply tsum_congr
      intro x
      rw [hcollapse x]
    _ = ∑ a, ∑' x, g a x * f a :=
      Summable.tsum_finsetSum (fun a ha => hgf a)
    _ = ∑ a, (∑' x, g a x) * f a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hg a).tsum_mul_right (f a)
    _ = ∑ a, (∑' x, μ x * (if ρ x = a then 1 else 0)) * f a := by
      rfl

private theorem summable_of_tsum_eq_one {α : Type*} (μ : α → ℝ)
    (hμ : (∑' x, μ x) = 1) : Summable μ := by
  by_contra hns
  rw [tsum_eq_zero_of_not_summable hns] at hμ
  norm_num at hμ

private theorem nuB_nonneg_le_of_probability (law : TailProductLaw) (V : ℕ)
    (hlawNonneg : ∀ σ, 0 ≤ law σ) (hlawTotal : (∑' σ, law σ) = 1)
    (hlawBound : ∀ σ, law σ ≠ 0 → σ ≤ V) (y : ℤ) :
    0 ≤ nuB law y ∧ nuB law y ≤ (V : ℝ) := by
  classical
  let f : ℕ → ℝ := fun σ => law σ * (σ : ℝ) * if (σ : ℤ) ∣ y then 1 else 0
  let g : ℕ → ℝ := fun σ => law σ * (V : ℝ)
  have hμsummable : Summable law := summable_of_tsum_eq_one law hlawTotal
  have hg : Summable g := by simpa [g] using hμsummable.mul_right (V : ℝ)
  have hfNonneg : ∀ σ, 0 ≤ f σ := by
    intro σ
    dsimp [f]
    exact mul_nonneg (mul_nonneg (hlawNonneg σ) (Nat.cast_nonneg σ))
      (by split_ifs <;> norm_num)
  have hfLe : ∀ σ, f σ ≤ g σ := by
    intro σ
    dsimp [f, g]
    by_cases hσ : law σ = 0
    · simp [hσ]
    · have hσV : (σ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hlawBound σ hσ
      by_cases hdiv : (σ : ℤ) ∣ y
      · simp only [if_pos hdiv, mul_one]
        exact mul_le_mul_of_nonneg_left hσV (hlawNonneg σ)
      · simp [hdiv]
        exact mul_nonneg (hlawNonneg σ) (Nat.cast_nonneg V)
  have hf : Summable f := hg.of_nonneg_of_le hfNonneg hfLe
  have hsumLE := Summable.tsum_le_tsum hfLe hf hg
  have hsumG : (∑' σ, g σ) = (V : ℝ) := by
    dsimp [g]
    rw [hμsummable.tsum_mul_right, hlawTotal]
    ring
  constructor
  · unfold nuB
    exact tsum_nonneg hfNonneg
  · change (∑' σ, f σ) ≤ (V : ℝ)
    rw [← hsumG]
    exact hsumLE

private theorem divisorTemplateLaw_probability {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (u : Fin q) :
    (∀ σ, 0 ≤ divisorTemplateLaw S.core.parameters N (D.divisor u) σ) ∧
    (∑' σ, divisorTemplateLaw S.core.parameters N (D.divisor u) σ = 1) := by
  classical
  let W := primorial (N + 1)
  let X : Fin (D.divisor u).arity → ℕ :=
    fun j => S.core.parameters.X N ((D.divisor u).cutoff j)
  have hW : 0 < W := by dsimp [W]; exact primorial_pos _
  have hX (j : Fin (D.divisor u).arity) : 0 < X j := by
    dsimp [X]
    exact S.core.parameters.Xpos N ((D.divisor u).cutoff j)
  have hH (j : Fin (D.divisor u).arity) : 0 < harmonicNormalizer (X j) W := by
    apply harmonicNormalizer_pos_of_cutoff (X j) W hW
    dsimp [X, W]
    exact S.gapStage.valid_raw_cutoffs N ((D.divisor u).cutoff j)
  have hmass := harmonicProductLaw_tsum_eq_one W X hX hH
  constructor
  · intro σ
    change 0 ≤ harmonicProductLaw W X σ
    unfold harmonicProductLaw
    apply tsum_nonneg
    intro t
    by_cases ht : (∏ j, t j) = σ
    · simp only [if_pos ht, one_mul]
      apply Finset.prod_nonneg
      intro j hj
      unfold harmonicNatLaw
      split_ifs with hn
      · have hnpos : (0 : ℝ) < (t j : ℝ) := by
          exact_mod_cast lt_of_lt_of_le (hX j) hn.1
        have hnormPos : 0 < harmonicNormalizer (X j) W := hH j
        positivity
      · simp
    · simp [ht]
  · change (∑' σ : ℕ, harmonicProductLaw W X σ) = 1
    exact hmass.1

private theorem divisorTemplateWeight_le {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (u : Fin q) (y : ℤ) :
    0 ≤ nuB (divisorTemplateLaw S.core.parameters N (D.divisor u)) y ∧
      nuB (divisorTemplateLaw S.core.parameters N (D.divisor u)) y ≤ (D.V N : ℝ) := by
  obtain ⟨hLawNonneg, hLawTotal⟩ := divisorTemplateLaw_probability D N u
  exact nuB_nonneg_le_of_probability
    (divisorTemplateLaw S.core.parameters N (D.divisor u)) (D.V N)
    hLawNonneg hLawTotal (D.divisor_bounded N u) y

private theorem baseResidue_expectation_error {d K : ℕ}
    (hK : 0 < K) (μ : (Fin d → ℤ) → ℝ) (hμ : (∑' x, μ x) = 1)
    (ε : ℝ) (f : (Fin d → Fin K) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ r, |f r| ≤ B)
    (hTV : finiteL1 (baseResidueLaw K hK μ) (uniformBaseResidueLaw K d) ≤ ε) :
    |(∑' x : Fin d → ℤ,
        μ x * f (fun i => integerResidue K hK (x i))) -
      ∑ r : Fin d → Fin K, uniformBaseResidueLaw K d r * f r| ≤ B * ε := by
  have hμsum : Summable μ := summable_of_tsum_eq_one μ hμ
  have hpush := tsum_pushforward_expectation μ
    (fun x => fun i => integerResidue K hK (x i)) hμsum f
  have hpush' :
      (∑' x : Fin d → ℤ, μ x * f (fun i => integerResidue K hK (x i))) =
        ∑ r : Fin d → Fin K, baseResidueLaw K hK μ r * f r := by
    simpa [baseResidueLaw] using hpush
  calc
    |(∑' x : Fin d → ℤ,
        μ x * f (fun i => integerResidue K hK (x i))) -
      ∑ r : Fin d → Fin K, uniformBaseResidueLaw K d r * f r| =
      |(∑ r : Fin d → Fin K,
          baseResidueLaw K hK μ r * f r) -
        ∑ r : Fin d → Fin K, uniformBaseResidueLaw K d r * f r| := by
          rw [hpush']
    _ ≤ B * finiteL1 (baseResidueLaw K hK μ) (uniformBaseResidueLaw K d) :=
      finiteL1_expectation_bound _ _ f B hB hf
    _ ≤ B * ε := mul_le_mul_of_nonneg_left hTV hB

private theorem finite_support_weighted_event_error {α : Type*} [DecidableEq α]
    (s : Finset α) (mass F : α → ℝ) (E : α → Prop) (δ : ℝ)
    (hmass : ∀ x ∈ s, 0 ≤ mass x) (hδ : 0 ≤ δ)
    (hF : ∀ x, E x → |F x - 1| ≤ δ) :
    |(∑ x ∈ s, mass x * (if E x then 1 else 0) * F x) -
      ∑ x ∈ s, mass x * (if E x then 1 else 0)| ≤
      δ * ∑ x ∈ s, mass x * (if E x then 1 else 0) := by
  have hrewrite :
      (∑ x ∈ s, mass x * (if E x then 1 else 0) * F x) -
        ∑ x ∈ s, mass x * (if E x then 1 else 0) =
      ∑ x ∈ s, mass x * (if E x then 1 else 0) * (F x - 1) := by
    calc
      _ = ∑ x ∈ s,
          (mass x * (if E x then 1 else 0) * F x - mass x * (if E x then 1 else 0)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hprobNonneg : 0 ≤ ∑ x ∈ s, mass x * (if E x then 1 else 0) := by
    apply Finset.sum_nonneg
    intro x hx
    by_cases hEx : E x <;> simp [hEx, hmass x hx]
  have hterm (x : α) (hx : x ∈ s) :
      |mass x * (if E x then 1 else 0) * (F x - 1)| ≤
        mass x * (if E x then 1 else 0) * δ := by
    by_cases hEx : E x
    · simp [hEx, abs_mul, abs_of_nonneg (hmass x hx)]
      exact mul_le_mul_of_nonneg_left (hF x hEx) (hmass x hx)
    · simp [hEx, hmass x hx]
  rw [hrewrite]
  calc
    |∑ x ∈ s, mass x * (if E x then 1 else 0) * (F x - 1)| ≤
        ∑ x ∈ s, mass x * (if E x then 1 else 0) * δ := by
      calc
        _ ≤ ∑ x ∈ s, |mass x * (if E x then 1 else 0) * (F x - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ s, mass x * (if E x then 1 else 0) * δ :=
          Finset.sum_le_sum fun x hx => hterm x hx
    _ = δ * ∑ x ∈ s, mass x * (if E x then 1 else 0) := by
      rw [← Finset.sum_mul]
      ring

private def linearFormsPrimeSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private def primePoolFiniteSupport (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter Nat.Prime

private theorem primePoolLaw_zero_of_not_mem_linearSupport (lo hi p : ℕ)
    (hp : p ∉ primePoolFiniteSupport lo hi) : primePoolLaw lo hi p = 0 := by
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hp (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩))
  · rfl

private theorem primePoolMass_nonneg_local (lo hi : ℕ) :
    0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  apply Finset.sum_nonneg
  intro p hp
  positivity

private theorem primePoolLaw_nonneg_local (lo hi p : ℕ) :
    0 ≤ primePoolLaw lo hi p := by
  unfold primePoolLaw
  split_ifs with h
  · exact div_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg p))
      (primePoolMass_nonneg_local lo hi)
  · simp

private theorem primePoolLaw_total_le_one (lo hi : ℕ) :
    ∑' p : ℕ, primePoolLaw lo hi p ≤ 1 := by
  classical
  let T := primePoolFiniteSupport lo hi
  have hzero (p : ℕ) (hp : p ∉ T) : primePoolLaw lo hi p = 0 :=
    primePoolLaw_zero_of_not_mem_linearSupport lo hi p (by simpa [T] using hp)
  rw [tsum_eq_sum (s := T) hzero]
  by_cases hS0 : primePoolMass lo hi = 0
  · have hTempty : T = ∅ := by
      by_contra hT
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
      have htermPos : 0 < 1 / (p : ℝ) := by positivity
      have hle : 1 / (p : ℝ) ≤ primePoolMass lo hi := by
        have hp' : p ∈ (Finset.Ico lo hi).filter Nat.Prime := by
          simpa [T, primePoolFiniteSupport] using hp
        change 1 / (p : ℝ) ≤
          ∑ r ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (r : ℝ)
        exact Finset.single_le_sum (f := fun r : ℕ => 1 / (r : ℝ))
          (fun r hr => by positivity) hp'
      rw [hS0] at hle
      linarith
    simp [T, hTempty]
  · have hSnonneg : 0 ≤ primePoolMass lo hi := by
      unfold primePoolMass
      apply Finset.sum_nonneg
      intro p hp
      positivity
    have hSpos : 0 < primePoolMass lo hi := lt_of_le_of_ne hSnonneg (Ne.symm hS0)
    have hsumLaw : ∑ p ∈ T, primePoolLaw lo hi p = 1 := by
      calc
        (∑ p ∈ T, primePoolLaw lo hi p) =
            ∑ p ∈ T, ((1 / (p : ℝ)) / primePoolMass lo hi) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hvalid : lo ≤ p ∧ p < hi ∧ p.Prime := by
            have hmem := Finset.mem_filter.mp hp
            exact ⟨Finset.mem_Ico.mp hmem.1 |>.1, Finset.mem_Ico.mp hmem.1 |>.2, hmem.2⟩
          simp [primePoolLaw, hvalid]
        _ = (∑ p ∈ T, 1 / (p : ℝ)) / primePoolMass lo hi := by
          rw [Finset.sum_div]
        _ = 1 := by
          rw [show (∑ p ∈ T, 1 / (p : ℝ)) = primePoolMass lo hi by
            simp [T, primePoolFiniteSupport, primePoolMass]]
          exact div_self (ne_of_gt hSpos)
    rw [hsumLaw]

private theorem independentPrimePoolMass_total_le_one {m : ℕ}
    (lo hi : Fin m → ℕ) :
    ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p ≤ 1 := by
  classical
  let S : Fin m → Finset ℕ := fun i => primePoolFiniteSupport (lo i) (hi i)
  let T : Finset (Fin m → ℕ) := Fintype.piFinset S
  have hzero (p : Fin m → ℕ) (hp : p ∉ T) :
      independentPrimePoolMass lo hi p = 0 := by
    have hnotall : ¬ ∀ i, p i ∈ S i := by
      intro hall
      exact hp (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hnotmem⟩ := not_forall.mp hnotall
    unfold independentPrimePoolMass
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact primePoolLaw_zero_of_not_mem_linearSupport (lo i) (hi i) (p i)
      (by simpa [S] using hnotmem)
  rw [tsum_eq_sum (s := T) hzero]
  have hsumPi :
      (∑ p ∈ T, independentPrimePoolMass lo hi p) =
        ∏ i, ∑ n ∈ S i, primePoolLaw (lo i) (hi i) n := by
    simpa [T, independentPrimePoolMass] using
      (Finset.prod_univ_sum S (fun i n => primePoolLaw (lo i) (hi i) n)).symm
  rw [hsumPi]
  have hbound := finset_prod_le_prod_of_nonneg Finset.univ
    (fun i => ∑ n ∈ S i, primePoolLaw (lo i) (hi i) n) (fun _ => (1 : ℝ))
    (by
      intro i hmem
      apply Finset.sum_nonneg
      intro n hn
      exact primePoolLaw_nonneg_local (lo i) (hi i) n)
    (by intro i hmem; positivity)
    (by
      intro i hmem
      have hle := primePoolLaw_total_le_one (lo i) (hi i)
      have hzero' (n : ℕ) (hn : n ∉ S i) : primePoolLaw (lo i) (hi i) n = 0 :=
        primePoolLaw_zero_of_not_mem_linearSupport (lo i) (hi i) n (by simpa [S] using hn)
      rw [tsum_eq_sum (s := S i) hzero'] at hle
      exact hle)
  simpa using hbound

private theorem independentPrimePoolMass_zero_of_not_mem_linearFormsSupport {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hp : p ∉ linearFormsPrimeSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin m, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [linearFormsPrimeSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private theorem primeCRT_expectation_error {m w V : ℕ}
    (lo hi : Fin m → ℕ) (f : (Fin m → CRTResidues w V) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ r, |f r| ≤ B) :
    |(∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
          f (fun i => integerCRTResidues w V (p i))) -
        ∑ r : Fin m → CRTResidues w V,
          uniformPrimeTupleCRTLaw w V r * f r| ≤
      B * finiteL1 (primeTupleCRTLaw lo hi w V) (uniformPrimeTupleCRTLaw w V) := by
  classical
  let T := linearFormsPrimeSupport lo hi
  have hzero (p : Fin m → ℕ) (hp : p ∉ T) :
      independentPrimePoolMass lo hi p = 0 :=
    independentPrimePoolMass_zero_of_not_mem_linearFormsSupport lo hi p
      (by simpa [T] using hp)
  have hμ : Summable (independentPrimePoolMass lo hi) := by
    apply summable_of_ne_finset_zero (s := T)
    intro p hp
    exact hzero p hp
  have hpush := tsum_pushforward_expectation (independentPrimePoolMass lo hi)
    (fun p => fun i => integerCRTResidues w V (p i)) hμ f
  have hpush' :
      (∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
        f (fun i => integerCRTResidues w V (p i))) =
        ∑ r : Fin m → CRTResidues w V,
          primeTupleCRTLaw lo hi w V r * f r := by
    simpa [primeTupleCRTLaw] using hpush
  calc
    |(∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
          f (fun i => integerCRTResidues w V (p i))) -
        ∑ r : Fin m → CRTResidues w V,
          uniformPrimeTupleCRTLaw w V r * f r| =
      |(∑ r : Fin m → CRTResidues w V,
          primeTupleCRTLaw lo hi w V r * f r) -
        ∑ r : Fin m → CRTResidues w V,
          uniformPrimeTupleCRTLaw w V r * f r| := by rw [hpush']
    _ ≤ B * finiteL1 (primeTupleCRTLaw lo hi w V)
        (uniformPrimeTupleCRTLaw w V) :=
      finiteL1_expectation_bound _ _ f B hB hf

private theorem finite_prime_support_event_error {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop)
    (F : (Fin m → ℕ) → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hF : ∀ p, E p → |F p - 1| ≤ δ)
    (htotal : ∑ p ∈ linearFormsPrimeSupport lo hi,
      independentPrimePoolMass lo hi p ≤ 1) :
    |(∑' p, independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p) -
      independentPrimePoolProbability lo hi E| ≤ δ := by
  classical
  let T := linearFormsPrimeSupport lo hi
  have hzeroF (p : Fin m → ℕ) (hp : p ∉ T) :
      independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p = 0 := by
    rw [independentPrimePoolMass_zero_of_not_mem_linearFormsSupport lo hi p (by simpa [T] using hp)]
    simp
  have hzeroE (p : Fin m → ℕ) (hp : p ∉ T) :
      independentPrimePoolMass lo hi p * (if E p then 1 else 0) = 0 := by
    rw [independentPrimePoolMass_zero_of_not_mem_linearFormsSupport lo hi p (by simpa [T] using hp)]
    simp
  have hmassNonneg (p : Fin m → ℕ) : 0 ≤ independentPrimePoolMass lo hi p := by
    have hpoolMassNonneg (i : Fin m) : 0 ≤ primePoolMass (lo i) (hi i) := by
      unfold primePoolMass
      apply Finset.sum_nonneg
      intro r hr
      positivity
    unfold independentPrimePoolMass
    apply Finset.prod_nonneg
    intro i hi
    unfold primePoolLaw
    split_ifs with h
    · have hpR : 0 < (p i : ℝ) := by exact_mod_cast h.2.2.pos
      exact div_nonneg (div_nonneg (by norm_num) hpR.le) (hpoolMassNonneg i)
    · simp
  have hprob :
      independentPrimePoolProbability lo hi E =
        ∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0) := by
    unfold independentPrimePoolProbability
    rw [tsum_eq_sum (s := T) hzeroE]
  have havg :
      (∑' p, independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p) =
        ∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p :=
    tsum_eq_sum (s := T) hzeroF
  have hprobLE :
      ∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ T, independentPrimePoolMass lo hi p :=
        Finset.sum_le_sum fun p hp => by by_cases hE : E p <;> simp [hE, hmassNonneg p]
      _ ≤ 1 := by simpa [T] using htotal
  calc
    |(∑' p, independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p) -
      independentPrimePoolProbability lo hi E| =
      |(∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0) * F p) -
        ∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0)| := by
          rw [havg, hprob]
    _ ≤ δ * ∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0) :=
      finite_support_weighted_event_error T (independentPrimePoolMass lo hi) F E δ
        (fun p hp => hmassNonneg p) hδ hF
    _ ≤ δ := by
      calc
        δ * (∑ p ∈ T, independentPrimePoolMass lo hi p * (if E p then 1 else 0)) ≤
            δ * 1 := mul_le_mul_of_nonneg_left hprobLE hδ
        _ = δ := by ring

private theorem alternating_powerset_card_sub_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    ∑ U ∈ s.powerset, (-1 : ℝ) ^ (s.card - U.card) = 0 := by
  have hsumZ : (∑ U ∈ s.powerset, (-1 : ℤ) ^ U.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  have hsum : (∑ U ∈ s.powerset, (-1 : ℝ) ^ U.card) = 0 := by
    exact_mod_cast hsumZ
  have hterm (U : Finset α) (hU : U ∈ s.powerset) :
      (-1 : ℝ) ^ (s.card - U.card) = (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ U.card := by
    have hle : U.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hU)
    have hexp : s.card - U.card + U.card = s.card := Nat.sub_add_cancel hle
    rcases neg_one_pow_eq_or ℝ U.card with hpow | hpow
    · rw [hpow, ← hexp, pow_add, hpow]
      simp
    · rw [hpow, ← hexp, pow_add, hpow]
      simp
  calc
    (∑ U ∈ s.powerset, (-1 : ℝ) ^ (s.card - U.card)) =
        ∑ U ∈ s.powerset, (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ U.card := by
          apply Finset.sum_congr rfl
          intro U hU
          exact hterm U hU
    _ = (-1 : ℝ) ^ s.card * ∑ U ∈ s.powerset, (-1 : ℝ) ^ U.card := by
          rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]

private def harmonicProductSupport {k : ℕ} (W : ℕ) (X : Fin k → ℕ) : Finset ℕ :=
  (Fintype.piFinset (fun i => harmonicNatSupport (X i) W)).image (fun t => ∏ i, t i)

private theorem harmonicProductLaw_zero_of_not_mem_support {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (σ : ℕ) (hσ : σ ∉ harmonicProductSupport W X) :
    harmonicProductLaw W X σ = 0 := by
  classical
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let product : (Fin k → ℕ) → ℕ := fun t => ∏ i, t i
  have hweightzero (t : Fin k → ℕ) (ht : t ∉ T) :
      ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ := harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have htermzero (t : Fin k → ℕ) (ht : t ∉ T) :
      (if product t = σ then 1 else 0) * ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    simp [hweightzero t ht]
  have hσ' : σ ∉ T.image product := by simpa [harmonicProductSupport, T, product, S] using hσ
  unfold harmonicProductLaw
  rw [tsum_eq_sum (s := T) htermzero]
  apply Finset.sum_eq_zero
  intro t ht
  have hne : product t ≠ σ := by
    intro heq
    exact hσ' (Finset.mem_image.mpr ⟨t, ht, heq⟩)
  simp [hne]

private def linearFormsPrimeAverage {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (p : Fin m → ℕ) : ℝ :=
  ∑' x : Fin d → ℤ, D.baseMass N p x *
    ∏ u, nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
      (linearRowValue D.rowCoeff N p u x).num

private theorem linearFormsPrimeAverage_bounds {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (p : Fin m → ℕ) :
    0 ≤ linearFormsPrimeAverage D N p ∧
      linearFormsPrimeAverage D N p ≤ (D.V N : ℝ) ^ q := by
  classical
  let μ : (Fin d → ℤ) → ℝ := D.baseMass N p
  let B : ℝ := (D.V N : ℝ)
  let F : (Fin d → ℤ) → ℝ := fun x =>
    ∏ u, nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
      (linearRowValue D.rowCoeff N p u x).num
  have hμtotal : (∑' x, μ x) = 1 := by
    simpa [μ] using D.base_normalized N p
  have hμsummable : Summable μ := summable_of_tsum_eq_one μ hμtotal
  have hμnonneg (x : Fin d → ℤ) : 0 ≤ μ x := by
    exact D.base_nonnegative N p x
  have hBnonneg : 0 ≤ B := by positivity
  have hFnonneg (x : Fin d → ℤ) : 0 ≤ F x := by
    dsimp [F]
    apply Finset.prod_nonneg
    intro u hu
    exact (divisorTemplateWeight_le D N u
      (linearRowValue D.rowCoeff N p u x).num).1
  have hFbound (x : Fin d → ℤ) : F x ≤ B ^ q := by
    have hprod := finset_prod_le_prod_of_nonneg Finset.univ
      (fun u => nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
        (linearRowValue D.rowCoeff N p u x).num)
      (fun _ => B)
      (by
        intro u hu
        exact (divisorTemplateWeight_le D N u
          (linearRowValue D.rowCoeff N p u x).num).1)
      (by intro u hu; exact hBnonneg)
      (by
        intro u hu
        exact (divisorTemplateWeight_le D N u
          (linearRowValue D.rowCoeff N p u x).num).2)
    simpa [F, B, Finset.prod_const, Fintype.card_fin] using hprod
  have htermNonneg (x : Fin d → ℤ) : 0 ≤ μ x * F x :=
    mul_nonneg (hμnonneg x) (hFnonneg x)
  have htermBound (x : Fin d → ℤ) : μ x * F x ≤ μ x * (B ^ q) :=
    mul_le_mul_of_nonneg_left (hFbound x) (hμnonneg x)
  have hboundSummable : Summable (fun x => μ x * (B ^ q)) :=
    hμsummable.mul_right (B ^ q)
  have htermSummable := hboundSummable.of_nonneg_of_le htermNonneg htermBound
  have hsumBound : (∑' x, μ x * (B ^ q)) = B ^ q := by
    rw [hμsummable.tsum_mul_right, hμtotal]
    ring
  constructor
  · change 0 ≤ ∑' x, μ x * F x
    exact tsum_nonneg htermNonneg
  · change (∑' x, μ x * F x) ≤ B ^ q
    calc
      (∑' x, μ x * F x) ≤ ∑' x, μ x * (B ^ q) :=
        Summable.tsum_le_tsum htermBound htermSummable hboundSummable
      _ = B ^ q := hsumBound

private theorem weightedLinearFormsAverage_bounds {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (E : (Fin m → ℕ) → Prop) :
    0 ≤ weightedLinearFormsAverage D N E ∧
      weightedLinearFormsAverage D N E ≤ (D.V N : ℝ) ^ q := by
  classical
  let lo : Fin m → ℕ := fun i => (S.primeStage.pool N (D.gap i)).lower
  let hi : Fin m → ℕ := fun i => (S.primeStage.pool N (D.gap i)).upper
  let T := linearFormsPrimeSupport lo hi
  let μ : (Fin m → ℕ) → ℝ := independentPrimePoolMass lo hi
  let B : ℝ := (D.V N : ℝ) ^ q
  have hB : 0 ≤ B := by positivity
  have hzero (p : Fin m → ℕ) (hp : p ∉ T) : μ p = 0 := by
    exact independentPrimePoolMass_zero_of_not_mem_linearFormsSupport lo hi p
      (by simpa [T] using hp)
  have hzeroAvg (p : Fin m → ℕ) (hp : p ∉ T) :
      μ p * (if E p then 1 else 0) * linearFormsPrimeAverage D N p = 0 := by
    rw [hzero p hp]
    simp
  have hmassNonneg (p : Fin m → ℕ) : 0 ≤ μ p := by
    unfold μ independentPrimePoolMass
    apply Finset.prod_nonneg
    intro i hmem
    exact primePoolLaw_nonneg_local (lo i) (hi i) (p i)
  have htotal := independentPrimePoolMass_total_le_one lo hi
  have htotalFin : (∑ p ∈ T, μ p) ≤ 1 := by
    have hzero' (p : Fin m → ℕ) (hp : p ∉ T) : μ p = 0 := hzero p hp
    rw [tsum_eq_sum (s := T) hzero'] at htotal
    simpa [T, μ] using htotal
  have haverage : weightedLinearFormsAverage D N E =
      ∑ p ∈ T, μ p * (if E p then 1 else 0) * linearFormsPrimeAverage D N p := by
    unfold weightedLinearFormsAverage
    change (∑' p, μ p * (if E p then 1 else 0) * linearFormsPrimeAverage D N p) = _
    rw [tsum_eq_sum (s := T) hzeroAvg]
  have haverageNonneg :
      0 ≤ ∑ p ∈ T, μ p * (if E p then 1 else 0) * linearFormsPrimeAverage D N p := by
    apply Finset.sum_nonneg
    intro p hp
    by_cases hE : E p
    · simp only [if_pos hE, mul_one]
      exact mul_nonneg (hmassNonneg p) (linearFormsPrimeAverage_bounds D N p).1
    · simp [hE]
  have haverageLe :
      (∑ p ∈ T, μ p * (if E p then 1 else 0) * linearFormsPrimeAverage D N p) ≤
        B * ∑ p ∈ T, μ p := by
    calc
      _ ≤ ∑ p ∈ T, μ p * B := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hE : E p
        · simp only [if_pos hE, mul_one]
          exact mul_le_mul_of_nonneg_left
            (linearFormsPrimeAverage_bounds D N p).2 (hmassNonneg p)
        · simp [hE]
          exact mul_nonneg (hmassNonneg p) hB
      _ = B * ∑ p ∈ T, μ p := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp; ring
  constructor
  · rw [haverage]
    exact haverageNonneg
  · rw [haverage]
    calc
      _ ≤ B * ∑ p ∈ T, μ p := haverageLe
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left htotalFin hB
      _ = B := by ring

private theorem linearFormsDivisorWeightExpansion {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (p : Fin m → ℕ) (x : Fin d → ℤ) :
    ∏ u, nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
        (linearRowValue D.rowCoeff N p u x).num =
      ∑ σ ∈ Fintype.piFinset (fun u => harmonicProductSupport
          (primorial (N + 1))
          (fun j => S.core.parameters.X N ((D.divisor u).cutoff j))),
        ∏ u, divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u) *
          (σ u : ℝ) *
          if (σ u : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0 := by
  classical
  let W := primorial (N + 1)
  let supp : Fin q → Finset ℕ := fun u =>
    harmonicProductSupport W (fun j => S.core.parameters.X N ((D.divisor u).cutoff j))
  let tupSupport := Fintype.piFinset supp
  have hnu (u : Fin q) :
      nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
        (linearRowValue D.rowCoeff N p u x).num =
      ∑ σ ∈ supp u,
        divisorTemplateLaw S.core.parameters N (D.divisor u) σ * (σ : ℝ) *
          if (σ : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0 := by
    have hzero (σ : ℕ) (hσ : σ ∉ supp u) :
        divisorTemplateLaw S.core.parameters N (D.divisor u) σ * (σ : ℝ) *
          (if (σ : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0) = 0 := by
      have hlaw : divisorTemplateLaw S.core.parameters N (D.divisor u) σ = 0 := by
        change harmonicProductLaw W
          (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)) σ = 0
        exact harmonicProductLaw_zero_of_not_mem_support W
          (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)) σ
          (by simpa [supp] using hσ)
      rw [hlaw]
      simp
    unfold nuB
    rw [tsum_eq_sum (s := supp u) hzero]
  calc
    (∏ u, nuB (divisorTemplateLaw S.core.parameters N (D.divisor u))
        (linearRowValue D.rowCoeff N p u x).num) =
        ∏ u, ∑ σ ∈ supp u,
          divisorTemplateLaw S.core.parameters N (D.divisor u) σ * (σ : ℝ) *
            (if (σ : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro u hu
      exact hnu u
    _ = ∑ σ ∈ tupSupport,
        ∏ u, divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u) *
          (σ u : ℝ) *
          (if (σ u : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0) := by
      simpa [tupSupport] using
        (Finset.prod_univ_sum supp
          (fun u σ => divisorTemplateLaw S.core.parameters N (D.divisor u) σ *
            (σ : ℝ) *
              (if (σ : ℤ) ∣ (linearRowValue D.rowCoeff N p u x).num then 1 else 0)))


/-- Expansion consequences with a uniform moment error: products of `1+ν_u` have main term
`2^q P(E)` up to the accumulated error, while any nonempty product with a factor `ν_u−1`
cancels up to the same error scale (§3 lines 666–678). -/
theorem divisor_weight_expansion_cancellation {q : ℕ}
    (P : ℝ) (moment : Finset (Fin q) → ℝ) (ε : ℝ)
    (hmain : ∀ S, |moment S - P| ≤ ε)
    (fixed minus plus : Finset (Fin q))
    (hdisj₁ : Disjoint fixed minus) (hdisj₂ : Disjoint fixed plus)
    (hdisj₃ : Disjoint minus plus) (hminus : minus.Nonempty) :
    (|∑ S : Finset (Fin q), moment S - (2 ^ q : ℕ) * P| ≤ (2 ^ q : ℕ) * ε) ∧
    (|∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
      (-1 : ℝ) ^ (minus.card - U.card) * moment (fixed ∪ S ∪ U)| ≤
        (2 ^ (plus.card + minus.card) : ℕ) * ε) := by
  constructor
  ·
    have hcard : (Finset.univ : Finset (Finset (Fin q))).card = 2 ^ q := by
      simp [Finset.card_powerset]
    have hsumErr :
        |∑ S : Finset (Fin q), (moment S - P)| ≤ (2 ^ q : ℝ) * ε := by
      calc
        |∑ S : Finset (Fin q), (moment S - P)| ≤
            ∑ S : Finset (Fin q), |moment S - P| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S : Finset (Fin q), ε := Finset.sum_le_sum fun S _ => hmain S
        _ = (2 ^ q : ℝ) * ε := by simp [Finset.sum_const, hcard]
    have hrewrite :
        (∑ S : Finset (Fin q), moment S) - (2 ^ q : ℕ) * P =
          ∑ S : Finset (Fin q), (moment S - P) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, hcard]
    rw [hrewrite]
    calc
      |∑ S : Finset (Fin q), (moment S - P)| ≤ (2 ^ q : ℝ) * ε := hsumErr
      _ = (2 ^ q : ℕ) * ε := by norm_cast
  ·
    have hzero := alternating_powerset_card_sub_zero minus hminus
    have hinner (S : Finset (Fin q)) :
        (∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * P) = 0 := by
      rw [← Finset.sum_mul, hzero]
      simp
    have hmainCancel :
        (∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * P) = 0 := by
      calc
        _ = ∑ S ∈ plus.powerset, (0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hinner S
        _ = 0 := by simp
    have hplusPowCast :
        (((2 : ℕ) ^ plus.card : ℕ) : ℝ) = (2 : ℝ) ^ plus.card := by
      rw [Nat.cast_pow]
      norm_num
    have hminusPowCast :
        (((2 : ℕ) ^ minus.card : ℕ) : ℝ) = (2 : ℝ) ^ minus.card := by
      rw [Nat.cast_pow]
      norm_num
    have hpowcast :
        (((2 : ℕ) ^ (plus.card + minus.card) : ℕ) : ℝ) =
          (2 : ℝ) ^ (plus.card + minus.card) := by
      rw [Nat.cast_pow]
      norm_num
    have hdecomp :
        (∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * moment (fixed ∪ S ∪ U)) =
        (∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * (moment (fixed ∪ S ∪ U) - P)) +
        (∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * P) := by
      calc
        _ = ∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
            ((-1 : ℝ) ^ (minus.card - U.card) *
              (moment (fixed ∪ S ∪ U) - P) +
             (-1 : ℝ) ^ (minus.card - U.card) * P) := by
          apply Finset.sum_congr rfl
          intro S hS
          apply Finset.sum_congr rfl
          intro U hU
          ring
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hsumErr :
        |∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * (moment (fixed ∪ S ∪ U) - P)| ≤
        (2 ^ (plus.card + minus.card) : ℝ) * ε := by
      calc
        _ ≤ ∑ S ∈ plus.powerset,
            |∑ U ∈ minus.powerset,
              (-1 : ℝ) ^ (minus.card - U.card) * (moment (fixed ∪ S ∪ U) - P)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
            |(-1 : ℝ) ^ (minus.card - U.card) *
              (moment (fixed ∪ S ∪ U) - P)| := by
          apply Finset.sum_le_sum
          intro S hS
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset, ε := by
          apply Finset.sum_le_sum
          intro S hS
          apply Finset.sum_le_sum
          intro U hU
          calc
            |(-1 : ℝ) ^ (minus.card - U.card) *
                (moment (fixed ∪ S ∪ U) - P)| =
              |moment (fixed ∪ S ∪ U) - P| := by simp
            _ ≤ ε := hmain (fixed ∪ S ∪ U)
        _ = (2 ^ (plus.card + minus.card) : ℝ) * ε := by
          calc
            _ = (plus.powerset.card : ℝ) * (minus.powerset.card : ℝ) * ε := by
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
            _ = (2 ^ plus.card : ℝ) * (2 ^ minus.card : ℝ) * ε := by
              rw [Finset.card_powerset plus, Finset.card_powerset minus]
              rw [hplusPowCast, hminusPowCast]
            _ = (2 ^ (plus.card + minus.card) : ℝ) * ε := by
              rw [pow_add]
    have hsumErrNat :
        |∑ S ∈ plus.powerset, ∑ U ∈ minus.powerset,
          (-1 : ℝ) ^ (minus.card - U.card) * (moment (fixed ∪ S ∪ U) - P)| ≤
        (2 ^ (plus.card + minus.card) : ℕ) * ε := by
      calc
        _ ≤ (2 : ℝ) ^ (plus.card + minus.card) * ε := hsumErr
        _ = (((2 : ℕ) ^ (plus.card + minus.card) : ℕ) : ℝ) * ε := by
          exact congrArg (fun z : ℝ => z * ε) hpowcast.symm
    rw [hdecomp, hmainCancel, add_zero]
    exact hsumErrNat

/-- Proposition `prop:linear-forms`: the weighted product of divisor weights has mean
`P(E)` up to the absolute error `O(1/w + V^q(ε_base+ε_CRT))`, uniformly over every
prime-only event `E⊆G`. The formulation permits rational rows with denominators that are
units modulo every possible divisor (§3 lines 463–519). -/
private def primeVectorMass (P : Finset ℕ) (law : ℕ → ℝ)
    (a : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, law n * (if ∀ p ∈ P, Nat.factorization n p = a p then 1 else 0)

private theorem independentPrimeVectorMass_eq {q : ℕ} (P : Finset ℕ)
    (laws : Fin q → ℕ → ℝ) (support : Fin q → Finset ℕ)
    (hlawZero : ∀ u n, n ∉ support u → laws u n = 0)
    (a : ℕ → Fin q → ℕ) :
    (∑' σ : Fin q → ℕ, (∏ u, laws u (σ u)) *
      (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0)) =
      ∏ u, primeVectorMass P (laws u) (fun p => a p u) := by
  classical
  let T : Finset (Fin q → ℕ) := Fintype.piFinset support
  let rowEvent (u : Fin q) (n : ℕ) : ℝ :=
    if ∀ p ∈ P, Nat.factorization n p = a p u then 1 else 0
  have hzero (σ : Fin q → ℕ) (hσ : σ ∉ T) :
      (∏ u, laws u (σ u)) *
        (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0) = 0 := by
    have hnot : ¬ ∀ u, σ u ∈ support u := by
      intro h
      exact hσ (Fintype.mem_piFinset.mpr h)
    obtain ⟨u, hu⟩ := not_forall.mp hnot
    rw [Finset.prod_eq_zero (Finset.mem_univ u) (hlawZero u (σ u) hu)]
    simp
  have hrowZero (u : Fin q) (n : ℕ) (hn : n ∉ support u) :
      laws u n * rowEvent u n = 0 := by
    rw [hlawZero u n hn]
    simp
  have hrowMass (u : Fin q) :
      primeVectorMass P (laws u) (fun p => a p u) =
        ∑ n ∈ support u, laws u n * rowEvent u n := by
    unfold primeVectorMass
    rw [tsum_eq_sum (s := support u) (hrowZero u)]
  have hindicator (σ : Fin q → ℕ) :
      (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0) =
        ∏ u, rowEvent u (σ u) := by
    by_cases h : ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u
    · have hrow : ∀ u, rowEvent u (σ u) = 1 := by
        intro u
        dsimp [rowEvent]
        rw [if_pos (h u)]
      rw [if_pos h]
      calc
        1 = ∏ u, (1 : ℝ) := by simp
        _ = ∏ u, rowEvent u (σ u) := by
          apply Finset.prod_congr rfl
          intro u hu
          rw [hrow u]
    · obtain ⟨u, hu⟩ := not_forall.mp h
      have hrow : rowEvent u (σ u) = 0 := by
        dsimp [rowEvent]
        rw [if_neg hu]
      rw [if_neg h]
      exact (Finset.prod_eq_zero (Finset.mem_univ u) hrow).symm
  calc
    (∑' σ : Fin q → ℕ, (∏ u, laws u (σ u)) *
      (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0)) =
        ∑ σ ∈ T, (∏ u, laws u (σ u)) *
          (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0) :=
      tsum_eq_sum (s := T) hzero
    _ = ∑ σ ∈ T, ∏ u, (laws u (σ u) * rowEvent u (σ u)) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hindicator]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ u, ∑ n ∈ support u, laws u n * rowEvent u n := by
      simpa [T] using (Finset.prod_univ_sum support
        (fun u n => laws u n * rowEvent u n)).symm
    _ = ∏ u, primeVectorMass P (laws u) (fun p => a p u) := by
      apply Finset.prod_congr rfl
      intro u hu
      rw [hrowMass u]

private theorem independentPrimeVectorMass_le {q : ℕ} (P : Finset ℕ)
    (laws : Fin q → ℕ → ℝ) (support : Fin q → Finset ℕ)
    (hlawZero : ∀ u n, n ∉ support u → laws u n = 0)
    (hlawNonneg : ∀ u n, 0 ≤ laws u n) (a : ℕ → Fin q → ℕ)
    (upper : Fin q → ℝ) (hupper : ∀ u, 0 ≤ upper u)
    (hrow : ∀ u, primeVectorMass P (laws u) (fun p => a p u) ≤ upper u) :
    (∑' σ : Fin q → ℕ, (∏ u, laws u (σ u)) *
      (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0)) ≤
        ∏ u, upper u := by
  rw [independentPrimeVectorMass_eq P laws support hlawZero a]
  exact finset_prod_le_prod_of_nonneg Finset.univ
    (fun u => primeVectorMass P (laws u) (fun p => a p u)) upper
    (by
      intro u hu
      unfold primeVectorMass
      apply tsum_nonneg
      intro n
      exact mul_nonneg (hlawNonneg u n) (by split_ifs <;> norm_num))
    (by intro u hu; exact hupper u)
    (by intro u hu; exact hrow u)

private theorem divisorTuplePrimeVectorMass_le {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N W : ℕ) (hW : 0 < W) (hWdef : W = primorial (N + 1))
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hcop : ∀ p ∈ P, Nat.Coprime p W)
    (hXscale : ∀ i : Fin n, 4 * W ≤ S.core.parameters.X N i)
    (hlog : ∀ i : Fin n, 4 * (W : ℝ) ≤ Real.log (S.core.parameters.X N i : ℝ))
    (a : ℕ → Fin q → ℕ) :
    (∑' σ : Fin q → ℕ,
      (∏ u, divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u)) *
        (if ∀ u, ∀ p ∈ P, Nat.factorization (σ u) p = a p u then 1 else 0)) ≤
      ∏ u, (6 : ℝ) ^ b * ∏ p ∈ P,
        (((a p u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a p u)) := by
  classical
  let laws : Fin q → ℕ → ℝ := fun u =>
    divisorTemplateLaw S.core.parameters N (D.divisor u)
  let support : Fin q → Finset ℕ := fun u =>
    harmonicProductSupport W
      (fun j => S.core.parameters.X N ((D.divisor u).cutoff j))
  have hlawZero (u : Fin q) (σ : ℕ) (hσ : σ ∉ support u) : laws u σ = 0 := by
    dsimp [laws, divisorTemplateLaw]
    rw [← hWdef]
    exact harmonicProductLaw_zero_of_not_mem_support W
      (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)) σ
      (by simpa [support] using hσ)
  have hXraw (u : Fin q) (j : Fin (D.divisor u).arity) :
      0 < S.core.parameters.X N ((D.divisor u).cutoff j) :=
    S.core.parameters.Xpos N ((D.divisor u).cutoff j)
  have hHraw (u : Fin q) (j : Fin (D.divisor u).arity) :
      0 < harmonicNormalizer
        (S.core.parameters.X N ((D.divisor u).cutoff j)) W := by
    apply harmonicNormalizer_pos_of_cutoff _ W hW
    exact hXscale ((D.divisor u).cutoff j)
  have hlawNonneg (u : Fin q) (σ : ℕ) : 0 ≤ laws u σ := by
    dsimp [laws, divisorTemplateLaw]
    rw [← hWdef]
    exact harmonicProductLaw_nonneg W
      (fun j => S.core.parameters.X N ((D.divisor u).cutoff j))
      (hXraw u) (hHraw u) σ
  let upper : Fin q → ℝ := fun u => (6 : ℝ) ^ b *
    ∏ p ∈ P, (((a p u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a p u))
  have hupper (u : Fin q) : 0 ≤ upper u := by
    dsimp [upper]
    positivity
  have hrow (u : Fin q) :
      primeVectorMass P (laws u) (fun p => a p u) ≤ upper u := by
    let Xraw : Fin (D.divisor u).arity → ℕ := fun j =>
      S.core.parameters.X N ((D.divisor u).cutoff j)
    have hlocal := harmonicProductLaw_primeVectorMass_le W P hprime hcop Xraw hW
      (fun j => hXraw u j)
      (fun j => hXscale ((D.divisor u).cutoff j))
      (fun j => hlog ((D.divisor u).cutoff j))
      (hHraw u) (fun p => a p u)
    have hprodLower :
        ∏ p ∈ P, (((a p u + 1 : ℕ) : ℝ) ^ (D.divisor u).arity /
          (p : ℝ) ^ (a p u)) ≤
        ∏ p ∈ P, (((a p u + 1 : ℕ) : ℝ) ^ b /
          (p : ℝ) ^ (a p u)) := by
      apply finset_prod_le_prod_of_nonneg
      · intro p hp
        positivity
      · intro p hp
        positivity
      · intro p hp
        have hB : (1 : ℝ) ≤ ((a p u + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ a p u + 1 by omega)
        have hpow := pow_le_pow_right₀ hB (D.divisor u).arity_le
        exact div_le_div_of_nonneg_right hpow (by positivity)
    have h6 : (6 : ℝ) ^ (D.divisor u).arity ≤ (6 : ℝ) ^ b :=
      pow_le_pow_right₀ (by norm_num) (D.divisor u).arity_le
    change primeVectorMass P (divisorTemplateLaw S.core.parameters N (D.divisor u))
      (fun p => a p u) ≤ upper u
    have hlocal' : primeVectorMass P (divisorTemplateLaw S.core.parameters N (D.divisor u))
        (fun p => a p u) ≤ (6 : ℝ) ^ (D.divisor u).arity *
          ∏ p ∈ P, (((a p u + 1 : ℕ) : ℝ) ^ (D.divisor u).arity /
            (p : ℝ) ^ (a p u)) := by
      simpa [primeVectorMass, Xraw, laws, divisorTemplateLaw, ← hWdef] using hlocal
    dsimp [upper]
    calc
      primeVectorMass P (divisorTemplateLaw S.core.parameters N (D.divisor u))
          (fun p => a p u) ≤ (6 : ℝ) ^ (D.divisor u).arity *
            ∏ p ∈ P, (((a p u + 1 : ℕ) : ℝ) ^ (D.divisor u).arity /
              (p : ℝ) ^ (a p u)) := hlocal'
      _ ≤ (6 : ℝ) ^ b * ∏ p ∈ P,
            (((a p u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a p u)) := by
          exact mul_le_mul h6 hprodLower (by positivity) (by positivity)
  exact independentPrimeVectorMass_le P laws support hlawZero hlawNonneg a upper hupper hrow

private theorem exists_top_two_positive_valuations {q : ℕ}
    (a : Fin q → ℕ)
    (hcard : 2 ≤ ((Finset.univ : Finset (Fin q)).filter fun u => 0 < a u).card) :
    ∃ u v : Fin q,
      0 < a u ∧ 0 < a v ∧ u ≠ v ∧ a v ≤ a u ∧
        ∀ w, w ≠ u → a w ≤ a v := by
  classical
  let U : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun u => 0 < a u
  have hcardU : 2 ≤ U.card := by simpa [U] using hcard
  have hUnonempty : U.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, huU, huMax⟩ := Finset.exists_max_image U a hUnonempty
  let R := U.erase u
  have hRcard : R.card = U.card - 1 := by
    dsimp [R]
    exact Finset.card_erase_of_mem huU
  have hRnonempty : R.Nonempty := by
    apply Finset.card_pos.mp
    rw [hRcard]
    omega
  obtain ⟨v, hvR, hvMax⟩ := Finset.exists_max_image R a hRnonempty
  have hvR' := Finset.mem_erase.mp hvR
  have huPos : 0 < a u := (Finset.mem_filter.mp huU).2
  have hvPos : 0 < a v := (Finset.mem_filter.mp hvR'.2).2
  refine ⟨u, v, huPos, hvPos, Ne.symm hvR'.1,
    huMax v hvR'.2, ?_⟩
  intro w hwu
  by_cases hw : 0 < a w
  · have hwU : w ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    exact hvMax w (Finset.mem_erase.mpr ⟨hwu, hwU⟩)
  · have hwa : a w = 0 := by omega
    omega

private def regularPrimeLocalExcessTerm {q : ℕ} (p : ℕ)
    (a : Fin q → ℕ) (u v : Fin q) : ℝ :=
  if u ≠ v ∧ 0 < a u ∧ 0 < a v ∧ a v ≤ a u ∧
      ∀ w, w ≠ u → a w ≤ a v then
    (p : ℝ) ^ ((∑ w, a w) - a u - a v) - 1 else 0

private def regularPrimeLocalExcess {q : ℕ} (p : ℕ) (a : Fin q → ℕ) : ℝ :=
  ∑ u : Fin q, ∑ v : Fin q, regularPrimeLocalExcessTerm p a u v

private def exceptionalPrimeLocalExcessTerm {q : ℕ} (p : ℕ)
    (a : Fin q → ℕ) (u : Fin q) : ℝ :=
  if 0 < a u ∧ ∀ v, v ≠ u → a v ≤ a u then
    (p : ℝ) ^ ((∑ w, a w) - a u) - 1 else 0

private def exceptionalPrimeLocalExcess {q : ℕ} (p : ℕ) (a : Fin q → ℕ) : ℝ :=
  ∑ u : Fin q, exceptionalPrimeLocalExcessTerm p a u

private theorem rowValuationPair_le_sum {q : ℕ} (a : Fin q → ℕ)
    (u v : Fin q) (huv : u ≠ v) :
    a u + a v ≤ ∑ w, a w := by
  have hsub : ({u, v} : Finset (Fin q)) ⊆ Finset.univ := by simp
  have hsum : (∑ w ∈ ({u, v} : Finset (Fin q)), a w) ≤ ∑ w, a w :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := a) hsub (by
    intro w hwU hwNot
    exact Nat.zero_le (a w))
  have hpair : (∑ w ∈ ({u, v} : Finset (Fin q)), a w) = a u + a v := by
    simp [huv, add_comm]
  rw [hpair] at hsum
  exact hsum

private theorem rowValuation_le_sum {q : ℕ} (a : Fin q → ℕ) (u : Fin q) :
    a u ≤ ∑ w, a w :=
  Finset.single_le_sum (f := a) (fun w hw => Nat.zero_le _) (Finset.mem_univ u)

private theorem regularPrimeLocalExcessTerm_nonneg {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) (u v : Fin q) : 0 ≤ regularPrimeLocalExcessTerm p a u v := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by
    have hpNat : 1 ≤ p := Nat.le_trans (by norm_num) hp.two_le
    exact_mod_cast hpNat
  unfold regularPrimeLocalExcessTerm
  split_ifs with h
  · have hsum := rowValuationPair_le_sum a u v h.1
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ ((∑ w, a w) - a u - a v) := one_le_pow₀ hpR
    linarith
  · norm_num

private theorem exceptionalPrimeLocalExcessTerm_nonneg {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) (u : Fin q) : 0 ≤ exceptionalPrimeLocalExcessTerm p a u := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by
    have hpNat : 1 ≤ p := Nat.le_trans (by norm_num) hp.two_le
    exact_mod_cast hpNat
  unfold exceptionalPrimeLocalExcessTerm
  split_ifs with h
  · have hsum := rowValuation_le_sum a u
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ ((∑ w, a w) - a u) := one_le_pow₀ hpR
    linarith
  · norm_num

private theorem regularPrimeLocalExcess_nonneg {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) : 0 ≤ regularPrimeLocalExcess p a := by
  classical
  unfold regularPrimeLocalExcess
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro v hv
  exact regularPrimeLocalExcessTerm_nonneg p hp a u v

private theorem exceptionalPrimeLocalExcess_nonneg {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) : 0 ≤ exceptionalPrimeLocalExcess p a := by
  classical
  unfold exceptionalPrimeLocalExcess
  apply Finset.sum_nonneg
  intro u hu
  exact exceptionalPrimeLocalExcessTerm_nonneg p hp a u

private theorem regularPrimeLocalExcessTerm_le {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) (u v : Fin q) :
    regularPrimeLocalExcessTerm p a u v ≤ regularPrimeLocalExcess p a := by
  classical
  have hinnerNonneg (x : Fin q) : 0 ≤ ∑ y : Fin q, regularPrimeLocalExcessTerm p a x y :=
    Finset.sum_nonneg fun y hy => regularPrimeLocalExcessTerm_nonneg p hp a x y
  have hv := Finset.single_le_sum
    (f := fun y => regularPrimeLocalExcessTerm p a u y)
    (fun y hy => regularPrimeLocalExcessTerm_nonneg p hp a u y) (Finset.mem_univ v)
  have hu := Finset.single_le_sum
    (f := fun x => ∑ y : Fin q, regularPrimeLocalExcessTerm p a x y)
    (fun x hx => hinnerNonneg x) (Finset.mem_univ u)
  exact hv.trans hu

private theorem exceptionalPrimeLocalExcessTerm_le {q : ℕ} (p : ℕ) (hp : p.Prime)
    (a : Fin q → ℕ) (u : Fin q) :
    exceptionalPrimeLocalExcessTerm p a u ≤ exceptionalPrimeLocalExcess p a := by
  classical
  have htermNonneg (x : Fin q) : 0 ≤ exceptionalPrimeLocalExcessTerm p a x :=
    exceptionalPrimeLocalExcessTerm_nonneg p hp a x
  exact Finset.single_le_sum (f := fun x => exceptionalPrimeLocalExcessTerm p a x)
    (fun x hx => htermNonneg x) (Finset.mem_univ u)

set_option maxHeartbeats 1000000 in
theorem localKernel_eq_one_of_atMostOnePositive {p A q d : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (hrow : ∀ u, ∃ j, IsUnit (coeff u j))
    (hsmall : ((Finset.univ : Finset (Fin q)).filter fun u => 0 < a u).card ≤ 1)
    [Fintype (Multiplicative (Fin d → ZMod (p ^ A)))]
    [Fintype (Multiplicative ((u : Fin q) → ZMod (p ^ (a u))))] :
    normalizedKernelCount (localDivisibilityAddHom a ha coeff).toMultiplicative = 1 := by
  classical
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI (u : Fin q) : NeZero (p ^ (a u)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  let f := (localDivisibilityAddHom a ha coeff).toMultiplicative
  have hbase := local_linear_kernel_count_excess f
  let U : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun u => 0 < a u
  have hUle : U.card ≤ 1 := by simpa [U] using hsmall
  by_cases hUempty : U = ∅
  · have hzero (u : Fin q) : a u = 0 := by
      by_contra hne
      have hu : u ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      rw [hUempty] at hu
      simp at hu
    haveI (u : Fin q) : Subsingleton (ZMod (p ^ (a u))) := by
      rw [hzero u]
      rw [pow_zero]
      exact (ZMod.subsingleton_iff).2 rfl
    haveI : Subsingleton ((u : Fin q) → ZMod (p ^ (a u))) := Pi.instSubsingleton
    haveI : Subsingleton (Multiplicative ((u : Fin q) → ZMod (p ^ (a u)))) := inferInstance
    have hsurj : Function.Surjective f := by
      intro y
      exact ⟨1, Subsingleton.elim _ _⟩
    exact hbase.2 hsurj
  · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
    have hUcard : U.card = 1 := by
      have hpos : 0 < U.card := hUne.card_pos
      omega
    obtain ⟨u, hUeq⟩ := Finset.card_eq_one.mp hUcard
    have huU : u ∈ U := by rw [hUeq]; simp
    have huPos : 0 < a u := (Finset.mem_filter.mp huU).2
    have hzero (v : Fin q) (hvu : v ≠ u) : a v = 0 := by
      by_contra hne
      have hvU : v ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hvEq : v = u := by
        rw [hUeq] at hvU
        simpa using hvU
      exact hvu hvEq
    obtain ⟨j, hj⟩ := hrow u
    have hupper := localKernel_upper_one_row hp a ha coeff u ⟨j, hj⟩
    have hprod : (∏ v : Fin q, (p : ℝ) ^ (a v)) = (p : ℝ) ^ (a u) := by
      simpa using (Finset.prod_eq_single_of_mem (s := Finset.univ) u
        (Finset.mem_univ u) (by
          intro v hv hvu
          rw [hzero v hvu]
          simp))
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hupperOne : normalizedKernelCount f ≤ 1 := by
      calc
        normalizedKernelCount f ≤
            (∏ v, (p : ℝ) ^ (a v)) / (p : ℝ) ^ (a u) := by
          change normalizedKernelCount
              (localDivisibilityAddHom a ha coeff).toMultiplicative ≤ _
          exact hupper
        _ = 1 := by rw [hprod]; exact div_self (ne_of_gt (pow_pos hpR _))
    exact le_antisymm hupperOne hbase.1

set_option maxHeartbeats 1000000 in
private theorem localKernel_regularExcess_bound {p A q d : ℕ}
    (hp : p.Prime) (hA : 0 < A) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (hrow : ∀ u, ∃ j, IsUnit (coeff u j))
    (hminor : ∀ u v, u ≠ v → ∃ i j,
      IsUnit (coeff u i * coeff v j - coeff u j * coeff v i))
    [Fintype (Multiplicative (Fin d → ZMod (p ^ A)))]
    [Fintype (Multiplicative ((u : Fin q) → ZMod (p ^ (a u))))] :
    normalizedKernelCount (localDivisibilityAddHom a ha coeff).toMultiplicative ≤
      1 + regularPrimeLocalExcess p a := by
  classical
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI (u : Fin q) : NeZero (p ^ (a u)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  let f := (localDivisibilityAddHom a ha coeff).toMultiplicative
  let U : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun u => 0 < a u
  by_cases hlarge : 2 ≤ U.card
  · obtain ⟨u, v, huPos, hvPos, huv, hvu, htop⟩ :=
      exists_top_two_positive_valuations a (by simpa [U] using hlarge)
    obtain ⟨i, j, hdet⟩ := hminor u v huv
    have hAmod : 1 < p ^ A := Nat.one_lt_pow (Nat.ne_of_gt hA) hp.one_lt
    letI : Fact (1 < p ^ A) := ⟨hAmod⟩
    have hij : i ≠ j := by
      intro heq
      subst j
      have hdet0 : IsUnit (0 : ZMod (p ^ A)) := by simpa using hdet
      have hunit : ((↑(hdet0.unit⁻¹) : ZMod (p ^ A)) * ↑hdet0.unit) = 1 := by
        simpa using Units.inv_val hdet0.unit
      have hzero : ((↑(hdet0.unit⁻¹) : ZMod (p ^ A)) * ↑hdet0.unit) = 0 := by
        rw [hdet0.unit_spec]
        simp
      exact one_ne_zero (hunit.symm.trans hzero)
    have htwo := localKernel_upper_two_rows hp a ha coeff u v i j hij hdet
    let total : ℕ := ∑ w, a w
    have hpairSum : a u + a v ≤ total := rowValuationPair_le_sum a u v huv
    have hprodPow : (∏ w : Fin q, (p : ℝ) ^ (a w)) = (p : ℝ) ^ total := by
      simp [total, Finset.prod_pow_eq_pow_sum]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpowRatio :
        (p : ℝ) ^ total / ((p : ℝ) ^ (a u) * (p : ℝ) ^ (a v)) =
          (p : ℝ) ^ (total - a u - a v) := by
      calc
        (p : ℝ) ^ total / ((p : ℝ) ^ (a u) * (p : ℝ) ^ (a v)) =
            (p : ℝ) ^ total / (p : ℝ) ^ (a u + a v) := by rw [pow_add]
        _ = (p : ℝ) ^ (total - (a u + a v)) := by
          simpa [div_eq_mul_inv] using
            (pow_sub₀ (p : ℝ) hpR hpairSum).symm
        _ = (p : ℝ) ^ (total - a u - a v) := by
          congr 1
          omega
    have hratio :
        (∏ w : Fin q, (p : ℝ) ^ (a w)) /
            ((p : ℝ) ^ (a u) * (p : ℝ) ^ (a v)) =
          (p : ℝ) ^ (total - a u - a v) := by
      simpa [hprodPow] using hpowRatio
    have hcond : u ≠ v ∧ 0 < a u ∧ 0 < a v ∧ a v ≤ a u ∧
        (∀ w, w ≠ u → a w ≤ a v) := ⟨huv, huPos, hvPos, hvu, htop⟩
    have htermVal : regularPrimeLocalExcessTerm p a u v =
        (p : ℝ) ^ (total - a u - a v) - 1 := by
      unfold regularPrimeLocalExcessTerm
      rw [if_pos hcond]
    have htermLE := regularPrimeLocalExcessTerm_le p hp a u v
    have hAlphaUpper : normalizedKernelCount f ≤
        (p : ℝ) ^ (total - a u - a v) := by
      calc
        normalizedKernelCount f ≤
            (∏ w : Fin q, (p : ℝ) ^ (a w)) /
              ((p : ℝ) ^ (a u) * (p : ℝ) ^ (a v)) := by
                change normalizedKernelCount
                    (localDivisibilityAddHom a ha coeff).toMultiplicative ≤ _
                exact htwo
        _ = _ := hratio
    calc
      normalizedKernelCount (localDivisibilityAddHom a ha coeff).toMultiplicative ≤
          (p : ℝ) ^ (total - a u - a v) := by
        simpa [f] using hAlphaUpper
      _ = 1 + ((p : ℝ) ^ (total - a u - a v) - 1) := by ring
      _ ≤ 1 + regularPrimeLocalExcess p a := by
        rw [← htermVal]
        nlinarith [htermLE]
  · have hsmall : U.card ≤ 1 := by omega
    have hEq := localKernel_eq_one_of_atMostOnePositive hp a ha coeff hrow (by
      simpa [U] using hsmall)
    rw [hEq]
    linarith [regularPrimeLocalExcess_nonneg p hp a]

set_option maxHeartbeats 1000000 in
private theorem localKernel_exceptionalExcess_bound {p A q d : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (coeff : Fin q → Fin d → ZMod (p ^ A))
    (hrow : ∀ u, ∃ j, IsUnit (coeff u j))
    [Fintype (Multiplicative (Fin d → ZMod (p ^ A)))]
    [Fintype (Multiplicative ((u : Fin q) → ZMod (p ^ (a u))))] :
    normalizedKernelCount (localDivisibilityAddHom a ha coeff).toMultiplicative ≤
      1 + exceptionalPrimeLocalExcess p a := by
  classical
  letI : NeZero (p ^ A) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  letI (u : Fin q) : NeZero (p ^ (a u)) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  let f := (localDivisibilityAddHom a ha coeff).toMultiplicative
  let U : Finset (Fin q) := (Finset.univ : Finset (Fin q)).filter fun u => 0 < a u
  by_cases hUempty : U = ∅
  · have hsmall : U.card ≤ 1 := by simp [U, hUempty]
    have hEq := localKernel_eq_one_of_atMostOnePositive hp a ha coeff hrow (by
      simpa [U] using hsmall)
    rw [hEq]
    linarith [exceptionalPrimeLocalExcess_nonneg p hp a]
  · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
    obtain ⟨u, huU, huMax⟩ := Finset.exists_max_image U a hUne
    have huPos : 0 < a u := (Finset.mem_filter.mp huU).2
    have htop : ∀ v, v ≠ u → a v ≤ a u := by
      intro v hvu
      by_cases hv : 0 < a v
      · have hvU : v ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        exact huMax v hvU
      · omega
    obtain ⟨j, hj⟩ := hrow u
    have hone := localKernel_upper_one_row hp a ha coeff u ⟨j, hj⟩
    let total : ℕ := ∑ v, a v
    have hsum : a u ≤ total := rowValuation_le_sum a u
    have hprodPow : (∏ v : Fin q, (p : ℝ) ^ (a v)) = (p : ℝ) ^ total := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ a (p : ℝ)
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpowRatio : (p : ℝ) ^ total / (p : ℝ) ^ (a u) =
        (p : ℝ) ^ (total - a u) := by
      simpa [div_eq_mul_inv] using
        (pow_sub₀ (p : ℝ) hpR hsum).symm
    have hratio : (∏ v : Fin q, (p : ℝ) ^ (a v)) / (p : ℝ) ^ (a u) =
        (p : ℝ) ^ (total - a u) := by
      simpa [hprodPow] using hpowRatio
    have hcond : 0 < a u ∧ ∀ v, v ≠ u → a v ≤ a u := ⟨huPos, htop⟩
    have htermVal : exceptionalPrimeLocalExcessTerm p a u =
        (p : ℝ) ^ (total - a u) - 1 := by
      unfold exceptionalPrimeLocalExcessTerm
      rw [if_pos hcond]
    have htermLE := exceptionalPrimeLocalExcessTerm_le p hp a u
    have hAlphaUpper : normalizedKernelCount f ≤ (p : ℝ) ^ (total - a u) := by
      calc
        normalizedKernelCount f ≤
            (∏ v : Fin q, (p : ℝ) ^ (a v)) / (p : ℝ) ^ (a u) := by
          change normalizedKernelCount
              (localDivisibilityAddHom a ha coeff).toMultiplicative ≤ _
          exact hone
        _ = _ := hratio
    calc
      normalizedKernelCount (localDivisibilityAddHom a ha coeff).toMultiplicative ≤
          (p : ℝ) ^ (total - a u) := by simpa [f] using hAlphaUpper
      _ = 1 + ((p : ℝ) ^ (total - a u) - 1) := by ring
      _ ≤ 1 + exceptionalPrimeLocalExcess p a := by
        rw [← htermVal]
        nlinarith [htermLE]

private theorem globalKernelPrimeProduct_bound {K q d : ℕ}
    (σ : Fin q → ℕ) (hσ : ∀ u, σ u ≠ 0) (hK : K ≠ 0)
    (hdiv : ∀ u, σ u ∣ K) (coeff : Fin q → Fin d → ZMod K)
    (P : Finset ℕ) (hP : K.primeFactors ⊆ P) (beta : ℕ → ℝ)
    (hbeta : ∀ p ∈ P, 0 ≤ beta p)
    [DecidableEq (primePowerIndex K)] [Fintype (primePowerIndex K)]
    [Fintype (Multiplicative (Fin d → ZMod K))]
    [Fintype (Multiplicative ((u : Fin q) → ZMod (σ u)))]
    [∀ p : primePowerIndex K,
      Fintype (Multiplicative (Fin d → ZMod (p.val ^ K.factorization p.val)))]
    [∀ p : primePowerIndex K,
      Fintype (Multiplicative ((u : Fin q) →
        ZMod (p.val ^ (σ u).factorization p.val)))]
    (hlower : ∀ p : primePowerIndex K, 1 ≤ normalizedKernelCount
      (localDivisibilityGroupHom
        (fun u => (σ u).factorization p.val)
        (fun u => ((Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)) p.val)
        (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p)))
    (hupper : ∀ p : primePowerIndex K,
      normalizedKernelCount
        (localDivisibilityGroupHom
          (fun u => (σ u).factorization p.val)
          (fun u => ((Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)) p.val)
          (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p)) ≤
        1 + beta p.val) :
    normalizedKernelCount (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative ≤
      ∏ p ∈ P, (1 + beta p) := by
  classical
  let localAlpha (p : primePowerIndex K) : ℝ := normalizedKernelCount
    (localDivisibilityGroupHom
      (fun u => (σ u).factorization p.val)
      (fun u => ((Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)) p.val)
      (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p))
  have hfactor : normalizedKernelCount (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative =
      ∏ p : primePowerIndex K, localAlpha p := by
    change normalizedKernelCount (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative =
      ∏ p : primePowerIndex K, normalizedKernelCount
        (localDivisibilityGroupHom
          (fun u => (σ u).factorization p.val)
          (fun u => ((Nat.factorization_le_iff_dvd (hσ u) hK).2 (hdiv u)) p.val)
          (fun u j => (primePowerCRTRingEquiv K hK (coeff u j)) p))
    exact globalDivisibility_normalizedKernelCount_factor σ hσ hK hdiv coeff
  have hlocalProd :
      (∏ p : primePowerIndex K, localAlpha p) ≤
        ∏ p : primePowerIndex K, (1 + beta p.val) := by
    apply finset_prod_le_prod_of_nonneg Finset.univ localAlpha (fun p => 1 + beta p.val)
    · intro p hp
      have hlow : 1 ≤ localAlpha p := by simpa [localAlpha] using hlower p
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hlow
    · intro p hp
      exact add_nonneg (by norm_num) (hbeta p.val (hP p.property))
    · intro p hp
      simpa [localAlpha] using hupper p
  have hsubtype :
      (∏ p : primePowerIndex K, (1 + beta p.val)) =
        ∏ p ∈ K.primeFactors, (1 + beta p) := by
    simpa [primePowerIndex] using
      (Finset.prod_subtype (p := fun p : ℕ => p ∈ K.primeFactors)
        (F := (inferInstance : Fintype (primePowerIndex K)))
        (s := K.primeFactors) (h := fun p : ℕ => Iff.rfl)
        (f := fun p : ℕ => 1 + beta p)).symm
  let extendedFactor : ℕ → ℝ := fun p => if p ∈ K.primeFactors then 1 + beta p else 1
  have hfull : (∏ p ∈ K.primeFactors, (1 + beta p)) ≤
      ∏ p ∈ P, (1 + beta p) := by
    have hleft : (∏ p ∈ K.primeFactors, (1 + beta p)) =
        ∏ p ∈ K.primeFactors, extendedFactor p := by
      apply Finset.prod_congr rfl
      intro p hp
      change 1 + beta p = extendedFactor p
      unfold extendedFactor
      rw [if_pos hp]
    have hsubset : (∏ p ∈ K.primeFactors, extendedFactor p) =
        ∏ p ∈ P, extendedFactor p := by
      exact Finset.prod_subset hP (by
        intro p hpP hpNot
        dsimp [extendedFactor]
        exact if_neg hpNot)
    have hright : (∏ p ∈ P, extendedFactor p) ≤
        ∏ p ∈ P, (1 + beta p) := by
      exact finset_prod_le_prod_of_nonneg P extendedFactor (fun p => 1 + beta p)
        (by
          intro p hp
          dsimp [extendedFactor]
          split_ifs with hpK
          · exact add_nonneg (by norm_num) (hbeta p hp)
          · norm_num)
        (by intro p hp; exact add_nonneg (by norm_num) (hbeta p hp))
        (by
          intro p hp
          by_cases hpK : p ∈ K.primeFactors
          · dsimp [extendedFactor]
            rw [if_pos hpK]
          · dsimp [extendedFactor]
            rw [if_neg hpK]
            exact le_add_of_nonneg_right (hbeta p hp))
    calc
      (∏ p ∈ K.primeFactors, (1 + beta p)) =
          ∏ p ∈ K.primeFactors, extendedFactor p := hleft
      _ = ∏ p ∈ P, extendedFactor p := hsubset
      _ ≤ ∏ p ∈ P, (1 + beta p) := hright
  have hmid : normalizedKernelCount (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative ≤
      ∏ p : primePowerIndex K, (1 + beta p.val) := by
    rw [hfactor]
    exact hlocalProd
  rw [hsubtype] at hmid
  exact hmid.trans hfull

set_option maxHeartbeats 1000000 in
private theorem uniformBaseKernelCount_eq_normalizedKernelCount {K q d : ℕ}
    (hK : 0 < K) [NeZero K] (σ : Fin q → ℕ) (hσ : ∀ u, 0 < σ u)
    [∀ u, NeZero (σ u)]
    (hKprod : ∏ u, σ u = K) (hdiv : ∀ u, σ u ∣ K)
    (coeff : Fin q → Fin d → ZMod K) :
    (∑ r : Fin d → Fin K,
      uniformBaseResidueLaw K d r *
        (if globalDivisibilityAddHom σ hdiv coeff
            (fun j => (ZMod.finEquiv K) (r j)) = 0 then (K : ℝ) else 0)) =
      normalizedKernelCount (globalDivisibilityAddHom σ hdiv coeff).toMultiplicative := by
  classical
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI (u : Fin q) : NeZero (σ u) := ⟨Nat.ne_of_gt (hσ u)⟩
  let g := globalDivisibilityAddHom σ hdiv coeff
  let f := g.toMultiplicative
  let e0 : Fin K ≃ ZMod K := (@ZMod.finEquiv K ⟨Nat.ne_of_gt hK⟩).toEquiv
  let e : (Fin d → Fin K) ≃ (Fin d → ZMod K) :=
    Equiv.piCongrRight (fun _ : Fin d => e0)
  let good : (Fin d → Fin K) → Prop := fun r => g (e r) = 0
  let eKer : {r : Fin d → Fin K // good r} ≃ f.ker := {
    toFun := fun (r : {r : Fin d → Fin K // good r}) =>
      (⟨Multiplicative.ofAdd (e r.val), by
      change Multiplicative.ofAdd (g (e r.val)) = 1
      rw [r.property]
      rfl⟩ : f.ker)
    invFun := fun (y : f.ker) =>
      (⟨e.symm y.val.toAdd, by
      have hy : f y.val = 1 := y.property
      have hzero : g y.val.toAdd = 0 := by
        have h := congrArg Multiplicative.toAdd hy
        simpa [f] using h
      simpa [good, e] using hzero⟩ : {r : Fin d → Fin K // good r})
    left_inv := by
      intro r
      apply Subtype.ext
      simp [e]
    right_inv := by
      intro y
      apply Subtype.ext
      change Multiplicative.ofAdd (e (e.symm y.val.toAdd)) = y.val
      simp [e]
    }
  have hcount :
      (∑ r : Fin d → Fin K, if good r then (1 : ℝ) else 0) =
        (Fintype.card f.ker : ℝ) := by
    have hcard : Fintype.card {r : Fin d → Fin K // good r} = Fintype.card f.ker :=
      Fintype.card_congr eKer
    calc
      (∑ r : Fin d → Fin K, if good r then (1 : ℝ) else 0) =
          (Fintype.card {r : Fin d → Fin K // good r} : ℝ) := by
            rw [Finset.sum_boole, Fintype.card_subtype]
      _ = (Fintype.card f.ker : ℝ) := by exact_mod_cast hcard
  have hcardH : (Fintype.card
      (Multiplicative ((u : Fin q) → ZMod (σ u))) : ℝ) = (K : ℝ) := by
    calc
      _ = (Fintype.card ((u : Fin q) → ZMod (σ u)) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = (∏ u, (Fintype.card (ZMod (σ u)) : ℝ)) := by
        exact_mod_cast (Fintype.card_pi :
          Fintype.card ((u : Fin q) → ZMod (σ u)) = ∏ u, Fintype.card (ZMod (σ u)))
      _ = ∏ u, (σ u : ℝ) := by simp [ZMod.card]
      _ = K := by exact_mod_cast hKprod
  have hcardG : (Fintype.card
      (Multiplicative (Fin d → ZMod K)) : ℝ) = (K : ℝ) ^ d := by
    calc
      _ = (Fintype.card (Fin d → ZMod K) : ℝ) := by
        exact_mod_cast Fintype.card_congr Multiplicative.toAdd
      _ = (K : ℝ) ^ d := by
        simp [Fintype.card_pi, ZMod.card]
  calc
    (∑ r : Fin d → Fin K,
      uniformBaseResidueLaw K d r *
        (if good r then (K : ℝ) else 0)) =
      (1 / (K : ℝ) ^ d) * (K : ℝ) *
        (∑ r : Fin d → Fin K, if good r then (1 : ℝ) else 0) := by
          unfold uniformBaseResidueLaw
          calc
            _ = ∑ r : Fin d → Fin K,
                (1 / (K : ℝ) ^ d) * (K : ℝ) * (if good r then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  by_cases hgood : good r <;> simp [hgood] <;> ring
            _ = _ := by rw [← Finset.mul_sum]
    _ = (Fintype.card (Multiplicative ((u : Fin q) → ZMod (σ u))) : ℝ) *
          ((Fintype.card f.ker : ℝ) / (Fintype.card
            (Multiplicative (Fin d → ZMod K)) : ℝ)) := by
          rw [hcount, hcardH, hcardG]
          ring
    _ = normalizedKernelCount f := by
      simp [normalizedKernelCount, localKernelProbability]

private theorem uniformUnitTupleMass_total (Q m : ℕ) (hQ : 0 < Q) :
    (∑ x : Fin m → Fin Q, uniformUnitTupleMass Q m x) = 1 := by
  classical
  let μ : Fin m → Fin Q → ℝ := fun _ x =>
    if Nat.Coprime x.val Q then 1 / (Nat.totient Q : ℝ) else 0
  have hmass (x : Fin m → Fin Q) : uniformUnitTupleMass Q m x = ∏ i, μ i (x i) := by
    by_cases hx : ∀ i, Nat.Coprime (x i).val Q
    · rw [uniformUnitTupleMass, if_pos hx]
      have hprod : ∏ i, μ i (x i) = (1 / (Nat.totient Q : ℝ)) ^ m := by
        calc
          ∏ i, μ i (x i) = ∏ _i : Fin m, (1 / (Nat.totient Q : ℝ)) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [μ, hx i]
          _ = (1 / (Nat.totient Q : ℝ)) ^ m := by
            simp [Finset.prod_const, Fintype.card_fin]
      rw [hprod]
      simp [one_div_pow]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      rw [uniformUnitTupleMass, if_neg hx]
      have hzero : μ i (x i) = 0 := by simp [μ, hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
  have hrow (i : Fin m) : (∑ x : Fin Q, μ i x) = 1 := by
    dsimp [μ]
    have hcard : (Finset.univ.filter (fun x : Fin Q => Nat.Coprime x.val Q)).card =
        Nat.totient Q := by
      let T : Finset ℕ := (Finset.range Q).filter (fun a => Nat.Coprime Q a)
      have hbij := Finset.card_bij (s := Finset.univ.filter
          (fun x : Fin Q => Nat.Coprime x.val Q)) (t := T)
        (fun x _ => x.val)
        (by
          intro x hx
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr x.isLt,
            (Finset.mem_filter.mp hx).2.symm⟩)
        (by
          intro x hx y hy heq
          exact Fin.ext heq)
        (by
          intro y hy
          have hy' := Finset.mem_filter.mp hy
          refine ⟨⟨y, Finset.mem_range.mp hy'.1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2.symm⟩, rfl⟩)
      rw [Nat.totient_eq_card_coprime]
      simpa [T, Nat.coprime_comm] using hbij
    have hφ : (Nat.totient Q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hQ))
    calc
      (∑ x : Fin Q, if Nat.Coprime x.val Q then 1 / (Nat.totient Q : ℝ) else 0) =
          ∑ x ∈ Finset.univ.filter (fun x : Fin Q => Nat.Coprime x.val Q),
            1 / (Nat.totient Q : ℝ) := by
              rw [Finset.sum_filter]
      _ = 1 := by simp [Finset.sum_const, hcard, hφ]
  calc
    (∑ x : Fin m → Fin Q, uniformUnitTupleMass Q m x) =
        ∑ x : Fin m → Fin Q, ∏ i, μ i (x i) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hmass x
    _ = ∏ i, ∑ x : Fin Q, μ i x := by
      let U : Fin m → Finset (Fin Q) := fun _ => Finset.univ
      simpa [U] using (Finset.prod_univ_sum U (fun i x => μ i x)).symm
    _ = 1 := by simp [hrow]

private theorem masterScale_tests_nonzero {n m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    (S : MasterScales n Aset m tests) :
    ∀ Q ∈ tests, Q ≠ 0 := by
  classical
  intro Q hQ hzero
  let f : ℕ → ℝ := fun N => uniformUnitTupleProbability
    ((primorial (N + 1)) ^ S.primeStage.e0 N) m
    (uniformSmallPrimeException tests (N + 1) (S.primeStage.e0 N))
  have hsmall : ∀ᶠ N : ℕ in atTop, f N < (1 / 2 : ℝ) :=
    S.primeStage.uniform_small_prime_exception.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hnever : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℕ)] with N hN hNlarge
    let w := N + 1
    let e := S.primeStage.e0 N
    have hepos : 1 ≤ e := S.primeStage.e0_pos N
    have htwo : Nat.Prime 2 := by norm_num
    have htwoW : 2 ≤ w := by dsimp [w]; omega
    have hdivW : 2 ∣ primorial w := htwo.dvd_primorial_iff.mpr htwoW
    have hall : ∀ x : Fin m → Fin ((primorial w) ^ e),
        uniformSmallPrimeException tests w e x := by
      intro x
      refine ⟨2, htwo, htwoW, Q, hQ, ?_⟩
      simp [hzero, evalIntegerPolynomial]
    have hmodpos : 0 < (primorial w) ^ e := Nat.pow_pos (primorial_pos w)
    have hprob : uniformUnitTupleProbability ((primorial w) ^ e) m
        (uniformSmallPrimeException tests w e) = 1 := by
      simp [uniformUnitTupleProbability, hall, uniformUnitTupleMass_total
        ((primorial w) ^ e) m hmodpos]
    have hf : f N = 1 := by simpa [f, w, e] using hprob
    rw [hf] at hN
    norm_num at hN
  obtain ⟨N, hNfalse⟩ := hnever.exists
  exact hNfalse

private theorem finCoprimeCard_prime (p : ℕ) (hp : p.Prime) :
    (Finset.univ.filter (fun x : Fin p => Nat.Coprime x.val p)).card = p - 1 := by
  classical
  let T : Finset ℕ := (Finset.range p).filter (fun a => Nat.Coprime p a)
  have hbij := Finset.card_bij (s := Finset.univ.filter
      (fun x : Fin p => Nat.Coprime x.val p)) (t := T)
    (fun x _ => x.val)
    (by
      intro x hx
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2.symm⟩)
    (by
      intro x hx y hy hxy
      exact Fin.ext hxy)
    (by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      refine ⟨⟨y, Finset.mem_range.mp hy'.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2.symm⟩, rfl⟩)
  have hTcard : T.card = Nat.totient p := by
    rfl
  have hcard : (Finset.univ.filter (fun x : Fin p => Nat.Coprime x.val p)).card =
      Nat.totient p := hbij.trans hTcard
  simpa [Nat.totient_prime hp] using hcard

set_option maxHeartbeats 20000000 in
private theorem uniformUnitTuple_polynomial_divisibility_bound {p m : ℕ}
    (hp : p.Prime) (Q : IntegerPolynomial m)
    (hQp : Q.map (Int.castRingHom (ZMod p)) ≠ 0) :
    uniformUnitTupleProbability p m
      (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ≤
        2 * (MvPolynomial.totalDegree Q : ℝ) / (p : ℝ) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let e0 : Fin p ≃ ZMod p := ZMod.finEquiv p
  let e : (Fin m → Fin p) ≃ (Fin m → ZMod p) :=
    Equiv.piCongrRight (fun _ : Fin m => e0)
  let unitFin : Finset (Fin p) :=
    Finset.univ.filter (fun x => Nat.Coprime x.val p)
  let unitTuples : Finset (Fin m → Fin p) :=
    Fintype.piFinset (fun _ : Fin m => unitFin)
  let U : Finset (ZMod p) := unitFin.image e0
  let T : Finset (Fin m → ZMod p) := Fintype.piFinset (fun _ : Fin m => U)
  let Qp : MvPolynomial (Fin m) (ZMod p) := Q.map (Int.castRingHom (ZMod p))
  let rootsFin : Finset (Fin m → Fin p) := unitTuples.filter
    (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val))
  let roots : Finset (Fin m → ZMod p) :=
    T.filter (fun z => MvPolynomial.eval z Qp = 0)
  have hUcard : U.card = p - 1 := by
    rw [Finset.card_image_iff.mpr e0.injective.injOn]
    exact finCoprimeCard_prime p hp
  have hUpos : 0 < U.card := by
    rw [hUcard]
    exact Nat.sub_pos_of_lt hp.two_le
  have hUmem (x : Fin p) : e0 x ∈ U ↔ Nat.Coprime x.val p := by
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
      have hEq : y = x := e0.injective hxy
      subst y
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      exact Finset.mem_image.mpr ⟨x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hunit (x : Fin m → Fin p) :
      (∀ i, Nat.Coprime (x i).val p) ↔ e x ∈ T := by
    constructor
    · intro hx
      apply Fintype.mem_piFinset.mpr
      intro i
      exact (hUmem (x i)).2 (hx i)
    · intro hx i
      exact (hUmem (x i)).1 (Fintype.mem_piFinset.mp hx i)
  have heval (x : Fin m → Fin p) :
      MvPolynomial.eval (e x) Qp =
        (evalIntegerPolynomial Q (fun i => (x i).val) : ZMod p) := by
    rw [MvPolynomial.eval_map]
    have harg : (fun i : Fin m => e0 (x i)) =
        fun i => ((x i).val : ZMod p) := by
      funext i
      cases p with
      | zero => exact (hp.ne_zero rfl).elim
      | succ p =>
          have hv : (e0 (x i)).val = (x i).val := rfl
          rw [← ZMod.natCast_zmod_val (e0 (x i)), hv]
    change MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun i => e0 (x i)) Q = _
    rw [harg]
    have hcomp := MvPolynomial.eval₂_comp_right (Int.castRingHom (ZMod p))
      (RingHom.id ℤ) (fun i => ((x i).val : ℤ)) Q
    have hcomp' : MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
        (fun i => ((x i).val : ZMod p)) Q =
        ((MvPolynomial.eval (fun i => ((x i).val : ℤ)) Q : ℤ) : ZMod p) := by
      have hfun : (Int.castRingHom (ZMod p) ∘ fun i : Fin m => ((x i).val : ℤ)) =
          fun i => ((x i).val : ZMod p) := by
        funext i
        simp [Function.comp_apply]
      rw [hfun] at hcomp
      simpa [MvPolynomial.map_id] using hcomp.symm
    simpa [evalIntegerPolynomial] using hcomp'
  let c : ℝ := 1 / (U.card : ℝ) ^ m
  have hunitFin (x : Fin m → Fin p) :
      (∀ i, Nat.Coprime (x i).val p) ↔ x ∈ unitTuples := by
    constructor
    · intro hx
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx i⟩
    · intro hx i
      exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx i)).2
  have hmass (x : Fin m → Fin p) :
      uniformUnitTupleMass p m x = if x ∈ unitTuples then c else 0 := by
    have hU := hunitFin x
    dsimp [c]
    simp only [uniformUnitTupleMass, Nat.totient_prime hp]
    by_cases hx : (∀ i, Nat.Coprime (x i).val p)
    · have hTx : x ∈ unitTuples := hU.mp hx
      simp [hx, hTx, hUcard]
    · have hTx : x ∉ unitTuples := fun h => hx (hU.mpr h)
      simp [hx, hTx, hUcard]
  have hprob : uniformUnitTupleProbability p m
      (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) =
        (rootsFin.card : ℝ) * c := by
    unfold uniformUnitTupleProbability
    calc
      _ = ∑ x : Fin m → Fin p, if x ∈ rootsFin then c else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hmass x]
        by_cases hu : x ∈ unitTuples
        · have hroot : ((p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ↔
              x ∈ rootsFin := by simp [rootsFin, hu]
          simp [hu, hroot]
        · simp [hu, rootsFin]
      _ = (rootsFin.card : ℝ) * c := by
        calc
          _ = ∑ x ∈ rootsFin, c := by
            calc
              _ = ∑ x ∈ Finset.univ, (if x ∈ rootsFin then c else 0) := rfl
              _ = ∑ x ∈ rootsFin, (if x ∈ rootsFin then c else 0) :=
                (Finset.sum_subset (Finset.subset_univ rootsFin) (by
                  intro x hx hxn
                  simp [hxn])).symm
              _ = ∑ x ∈ rootsFin, c := by
                apply Finset.sum_congr rfl
                intro x hx
                simp [hx]
          _ = (rootsFin.card : ℝ) * c := by simp [Finset.sum_const]
  have hdiv (x : Fin m → Fin p) :
      ((p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ↔
        MvPolynomial.eval (e x) Qp = 0 := by
    rw [heval x]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
  have hrootsCard : rootsFin.card = roots.card := by
    apply Finset.card_bijective e e.bijective
    intro x
    simp only [rootsFin, roots, Finset.mem_filter]
    exact and_congr ((hunitFin x).symm.trans (hunit x)) (hdiv x)
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hQp U
  have hszR : (roots.card : ℝ) / (U.card : ℝ) ^ m ≤
      (Qp.totalDegree : ℝ) / (U.card : ℝ) := by
    have hsz' : (roots.card : ℚ≥0) / (U.card : ℚ≥0) ^ m ≤
        (Qp.totalDegree : ℚ≥0) / (U.card : ℚ≥0) := by
      simpa [roots, T, Qp] using hsz
    have hszQ : (roots.card : ℚ) / (U.card : ℚ) ^ m ≤
        (Qp.totalDegree : ℚ) / (U.card : ℚ) := by
      exact_mod_cast (NNRat.coe_le_coe.mp hsz')
    have hszCast := (Rat.cast_le (K := ℝ)).2 hszQ
    simpa [Nat.cast_pow] using hszCast
  have hdeg : Qp.totalDegree ≤ Q.totalDegree := by
    change (MvPolynomial.map (Int.castRingHom (ZMod p)) Q).totalDegree ≤ Q.totalDegree
    have hsupp : (MvPolynomial.map (Int.castRingHom (ZMod p)) Q).support ⊆ Q.support :=
      MvPolynomial.support_map_subset (f := Int.castRingHom (ZMod p)) Q
    simpa only [MvPolynomial.totalDegree] using Finset.sup_mono hsupp
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hUreal : 0 < (U.card : ℝ) := by exact_mod_cast hUpos
  have hratio : 1 / (U.card : ℝ) ≤ 2 / (p : ℝ) := by
    rw [hUcard]
    have hpNat : p ≤ 2 * (p - 1) := by omega
    have hpNatR : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hpNat
    apply (div_le_div_iff₀ (by exact_mod_cast (Nat.sub_pos_of_lt hp.two_le)) hpR).2
    simpa using hpNatR
  calc
    uniformUnitTupleProbability p m
        (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) =
        (roots.card : ℝ) / (U.card : ℝ) ^ m := by
          rw [hprob, hrootsCard]
          dsimp [c]
          ring
    _ ≤ (Qp.totalDegree : ℝ) / (U.card : ℝ) := hszR
    _ ≤ (Q.totalDegree : ℝ) / (U.card : ℝ) := by
          gcongr
    _ ≤ 2 * (Q.totalDegree : ℝ) / (p : ℝ) := by
          calc
            (Q.totalDegree : ℝ) / (U.card : ℝ) =
                (Q.totalDegree : ℝ) * (1 / (U.card : ℝ)) := by ring
            _ ≤ (Q.totalDegree : ℝ) * (2 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = 2 * (Q.totalDegree : ℝ) / (p : ℝ) := by ring

private def integerPolynomialContent {m : ℕ} (Q : IntegerPolynomial m) : ℕ :=
  ∑ c ∈ Q.coeffs, c.natAbs

private theorem integerPolynomial_map_zmod_ne_zero_of_content_lt {p m : ℕ}
    (hp : p.Prime) (Q : IntegerPolynomial m) (hQ : Q ≠ 0)
    (hcontent : integerPolynomialContent Q < p) :
    Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  classical
  intro hmap
  obtain ⟨e, he⟩ := Q.support_nonempty.mpr hQ
  have hcoeff : Q.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hcoeffMem : Q.coeff e ∈ Q.coeffs := MvPolynomial.coeff_mem_coeffs e hcoeff
  have hcoeffBound : (Q.coeff e).natAbs ≤ integerPolynomialContent Q := by
    unfold integerPolynomialContent
    exact Finset.single_le_sum (f := fun c : ℤ => c.natAbs)
      (by intro c hc; exact Nat.zero_le _) hcoeffMem
  have hcastZero : (Q.coeff e : ZMod p) = 0 := by
    have hcoeffMap : (Q.map (Int.castRingHom (ZMod p))).coeff e =
        (Q.coeff e : ZMod p) := MvPolynomial.coeff_map _ _ _
    rw [← hcoeffMap, hmap]
    simp
  have hdvdInt : (p : ℤ) ∣ Q.coeff e :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcastZero
  have hdvdNat : p ∣ (Q.coeff e).natAbs := Int.natCast_dvd.mp hdvdInt
  have hnatPos : 0 < (Q.coeff e).natAbs := Int.natAbs_pos.mpr hcoeff
  have hpLe : p ≤ (Q.coeff e).natAbs := Nat.le_of_dvd hnatPos hdvdNat
  omega

private theorem uniformUnitTupleProbability_le_one {p m : ℕ} (hp : p.Prime)
    (E : (Fin m → Fin p) → Prop) :
    uniformUnitTupleProbability p m E ≤ 1 := by
  classical
  have hmassNonneg (x : Fin m → Fin p) : 0 ≤ uniformUnitTupleMass p m x := by
    unfold uniformUnitTupleMass
    split_ifs
    · positivity
    · simp
  calc
    uniformUnitTupleProbability p m E ≤ ∑ x : Fin m → Fin p, uniformUnitTupleMass p m x := by
      unfold uniformUnitTupleProbability
      apply Finset.sum_le_sum
      intro x hx
      by_cases hE : E x <;> simp [hE, hmassNonneg x]
    _ = 1 := uniformUnitTupleMass_total p m hp.pos

private theorem if_decidable_irrel (P : Prop) (d₁ d₂ : Decidable P) (a b : ℝ) :
    @ite ℝ P d₁ a b = @ite ℝ P d₂ a b := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  cases h
  rfl

private theorem uniformUnitTuple_testBad_probability_bound {p m : ℕ}
    (hp : p.Prime) (tests : Finset (IntegerPolynomial m))
    (htests : ∀ Q ∈ tests, Q ≠ 0) (B : ℕ) (hB : 0 < B)
    (hsize : ∀ Q ∈ tests, integerPolynomialContent Q < B ∧
      Q.totalDegree ≤ B) :
    uniformUnitTupleProbability p m
      (fun x => ∃ Q ∈ tests,
        (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ≤
      2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / (p : ℝ) := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hpB : p ≤ B
  · have hprob := uniformUnitTupleProbability_le_one hp
      (fun x => ∃ Q ∈ tests,
        (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val))
    have hratio : (1 : ℝ) ≤ 2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / (p : ℝ) := by
      have hpB' : (p : ℝ) ≤ (B : ℝ) := by exact_mod_cast hpB
      have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
      have hcard : (1 : ℝ) ≤ ((tests.card + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ tests.card + 1)
      rw [le_div_iff₀ hpR]
      nlinarith
    exact hprob.trans hratio
  · have hpB' : B < p := Nat.lt_of_not_ge hpB
    have hroot (Q : IntegerPolynomial m) (hQ : Q ∈ tests) :
        uniformUnitTupleProbability p m
          (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ≤
        2 * (Q.totalDegree : ℝ) / (p : ℝ) := by
      have hred := integerPolynomial_map_zmod_ne_zero_of_content_lt hp Q
        (htests Q hQ) (Nat.lt_trans (hsize Q hQ).1 hpB')
      exact uniformUnitTuple_polynomial_divisibility_bound hp Q hred
    have hunion : uniformUnitTupleProbability p m
        (fun x => ∃ Q ∈ tests,
          (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ≤
        ∑ Q ∈ tests, uniformUnitTupleProbability p m
          (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) := by
      unfold uniformUnitTupleProbability
      calc
        _ ≤ ∑ x : Fin m → Fin p,
              uniformUnitTupleMass p m x *
              (∑ Q ∈ tests,
                if (fun y : Fin m → Fin p =>
                    (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                  (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro x hx
              have hmassNonneg : 0 ≤ uniformUnitTupleMass p m x := by
                unfold uniformUnitTupleMass
                split_ifs <;> positivity
              have hindicator :
                  (if (fun y : Fin m → Fin p => ∃ Q ∈ tests,
                    (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                    (1 : ℝ) else 0) ≤
                    ∑ Q ∈ tests,
                      if (fun y : Fin m → Fin p =>
                        (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                        (1 : ℝ) else 0 := by
                letI : Decidable ((fun y : Fin m → Fin p => ∃ Q ∈ tests,
                    (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x) :=
                  Classical.propDecidable _
                by_cases h : (fun y : Fin m → Fin p => ∃ Q ∈ tests,
                    (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x
                · simp only [if_pos h]
                  obtain ⟨Q, hQ, hdiv⟩ := h
                  have hsingle := Finset.single_le_sum (f := fun Q =>
                    if (fun y : Fin m → Fin p =>
                      (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                      (1 : ℝ) else 0)
                    (by intro Q hQ'; split_ifs <;> norm_num) hQ
                  calc
                    (1 : ℝ) = (if (p : ℤ) ∣ evalIntegerPolynomial Q
                        (fun i => (x i).val) then 1 else 0) := (if_pos hdiv).symm
                    _ ≤ ∑ Q ∈ tests,
                        if (fun y : Fin m → Fin p =>
                          (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                          (1 : ℝ) else 0 := hsingle
                · simp [h]
              have hmul := mul_le_mul_of_nonneg_left hindicator hmassNonneg
              let P : Prop := (fun y : Fin m → Fin p => ∃ Q ∈ tests,
                (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x
              have hite : @ite ℝ P (inferInstance : Decidable P) 1 0 =
                  @ite ℝ P (Classical.propDecidable P) 1 0 :=
                if_decidable_irrel P _ _ _ _
              rw [hite] at hmul
              exact hmul
        _ = ∑ x : Fin m → Fin p, ∑ Q ∈ tests,
              uniformUnitTupleMass p m x *
                (if (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val) then
                  (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
        _ = ∑ Q ∈ tests, ∑ x : Fin m → Fin p,
              uniformUnitTupleMass p m x *
                (if (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val) then
                  (1 : ℝ) else 0) := by
              change (∑ x : Fin m → Fin p, ∑ Q ∈ tests,
                  uniformUnitTupleMass p m x *
                    (if (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val) then
                      (1 : ℝ) else 0)) = _
              exact Finset.sum_comm (s := Finset.univ) (t := tests)
                (f := fun x Q => uniformUnitTupleMass p m x *
                  (if (fun y : Fin m → Fin p =>
                    (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (y i).val)) x then
                    (1 : ℝ) else 0))
        _ = ∑ Q ∈ tests, uniformUnitTupleProbability p m
              (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) := by
              unfold uniformUnitTupleProbability
              apply Finset.sum_congr rfl
              intro Q hQ
              apply Finset.sum_congr rfl
              intro x hx
              let P : Prop := (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)
              have hite : @ite ℝ P (inferInstance : Decidable P) 1 0 =
                  @ite ℝ P (Classical.propDecidable P) 1 0 :=
                if_decidable_irrel P _ _ _ _
              rw [hite]
    have hdegreeSum :
        (∑ Q ∈ tests, (Q.totalDegree : ℝ)) ≤
          ((tests.card : ℝ) * (B : ℝ)) := by
      calc
        (∑ Q ∈ tests, (Q.totalDegree : ℝ)) ≤ ∑ _Q ∈ tests, (B : ℝ) := by
          apply Finset.sum_le_sum
          intro Q hQ
          exact_mod_cast (hsize Q hQ).2
        _ = (tests.card : ℝ) * (B : ℝ) := by simp
    calc
      uniformUnitTupleProbability p m
          (fun x => ∃ Q ∈ tests,
            (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) ≤
          ∑ Q ∈ tests, uniformUnitTupleProbability p m
            (fun x => (p : ℤ) ∣ evalIntegerPolynomial Q (fun i => (x i).val)) := hunion
      _ ≤ ∑ Q ∈ tests, 2 * (Q.totalDegree : ℝ) / (p : ℝ) := by
          apply Finset.sum_le_sum
          intro Q hQ
          exact hroot Q hQ
      _ = 2 * (∑ Q ∈ tests, (Q.totalDegree : ℝ)) / (p : ℝ) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ 2 * ((tests.card : ℝ) * (B : ℝ)) / (p : ℝ) := by
          gcongr
      _ ≤ 2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / (p : ℝ) := by
          apply div_le_div_of_nonneg_right _ hpR.le
          have hcard : (tests.card : ℝ) ≤ ((tests.card + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ tests.card
          have hBreal : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
          nlinarith

private theorem piProductMarginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (hμ : ∀ i, ∑ x, μ i x = 1)
    (i₀ : ι) (f : α i₀ → ℝ) :
    (∑ x : ∀ i, α i, (∏ i, μ i (x i)) * f (x i₀)) =
      ∑ y : α i₀, μ i₀ y * f y := by
  classical
  let J := {i : ι // i ≠ i₀}
  letI : Fintype J := Fintype.ofFinite J
  have hsubtype (x : ∀ i, α i) :
      (∏ j : J, μ j.val (x j.val)) =
        ∏ j ∈ (Finset.univ.erase i₀), μ j (x j) := by
    simpa [J] using
      (Finset.prod_subtype (p := fun j : ι => j ≠ i₀)
        (F := (inferInstance : Fintype J)) (s := Finset.univ.erase i₀)
        (h := fun j => by simp [Finset.mem_erase])
        (f := fun j => μ j (x j))).symm
  have hprodSplit (x : ∀ i, α i) :
      (∏ i, μ i (x i)) = μ i₀ (x i₀) * ∏ j : J, μ j.val (x j.val) := by
    calc
      (∏ i, μ i (x i)) =
          μ i₀ (x i₀) * ∏ i ∈ (Finset.univ.erase i₀), μ i (x i) := by
            rw [← Finset.mul_prod_erase (Finset.univ) (fun i => μ i (x i))
              (Finset.mem_univ i₀)]
      _ = μ i₀ (x i₀) * ∏ j : J, μ j.val (x j.val) := by rw [← hsubtype x]
  have hrest :
      (∑ y : ∀ j : J, α j.val, ∏ j : J, μ j.val (y j)) = 1 := by
    let s : ∀ j : J, Finset (α j.val) := fun _ => Finset.univ
    calc
      _ = ∏ j : J, ∑ z : α j.val, μ j.val z := by
        simpa [s] using (Finset.prod_univ_sum s (fun j z => μ j.val z)).symm
      _ = 1 := by simp [hμ]
  let e : (∀ i, α i) ≃ (α i₀ × ∀ j : J, α j.val) := Equiv.piSplitAt i₀ α
  let g : α i₀ × (∀ j : J, α j.val) → ℝ := fun y =>
    (μ i₀ y.1 * f y.1) * ∏ j : J, μ j.val (y.2 j)
  calc
    (∑ x : ∀ i, α i, (∏ i, μ i (x i)) * f (x i₀)) =
        ∑ y : α i₀ × (∀ j : J, α j.val), g y := by
          apply Fintype.sum_equiv e
          intro x
          rw [hprodSplit x]
          simp [g, e, Equiv.piSplitAt, mul_assoc, mul_comm, mul_left_comm]
    _ = (∑ y : α i₀, μ i₀ y * f y) *
          (∑ z : ∀ j : J, α j.val, ∏ j : J, μ j.val (z j)) := by
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ y : α i₀, (μ i₀ y * f y) *
                (∑ z : ∀ j : J, α j.val, ∏ j : J, μ j.val (z j)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.mul_sum]
          _ = _ := by rw [← Finset.sum_mul]
    _ = ∑ y : α i₀, μ i₀ y * f y := by rw [hrest]; ring

private def crtSlotPrimeSwapEquiv {m w V : ℕ} :
    (Fin m → CRTResidues w V) ≃
      (∀ p : CRTPrimeRange w V, Fin m → Fin p.val) where
  toFun r p i := r i p
  invFun s i p := s p i
  left_inv r := by funext i p; rfl
  right_inv s := by funext p i; rfl

private theorem uniformPrimeTupleCRTLaw_factor {m w V : ℕ}
    (s : ∀ p : CRTPrimeRange w V, Fin m → Fin p.val) :
    uniformPrimeTupleCRTLaw w V (fun i p => s p i) =
      ∏ p : CRTPrimeRange w V, uniformUnitTupleMass p.val m (s p) := by
  classical
  unfold uniformPrimeTupleCRTLaw
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
  by_cases hunit : ∀ i, Nat.Coprime (s p i).val p.val
  · have hprod : (∏ i, if Nat.Coprime (s p i).val p.val then
        1 / ((p.val - 1 : ℕ) : ℝ) else 0) =
        (1 / ((p.val - 1 : ℕ) : ℝ)) ^ m := by
      calc
        _ = ∏ _i : Fin m, (1 / ((p.val - 1 : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [hunit i]
        _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
    have hmass : uniformUnitTupleMass p.val m (s p) =
        (1 / ((p.val - 1 : ℕ) : ℝ)) ^ m := by
      simp [uniformUnitTupleMass, hunit, Nat.totient_prime hpPrime, one_div_pow]
    exact hprod.trans hmass.symm
  · obtain ⟨i, hi⟩ := not_forall.mp hunit
    have hprod : (∏ i, if Nat.Coprime (s p i).val p.val then
        1 / ((p.val - 1 : ℕ) : ℝ) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    have hmass : uniformUnitTupleMass p.val m (s p) = 0 := by
      simp [uniformUnitTupleMass, hunit, Nat.totient_prime hpPrime]
    exact hprod.trans hmass.symm

private theorem uniformPrimeTupleCRTLaw_marginal {m w V : ℕ}
    (p₀ : CRTPrimeRange w V) (E : (Fin m → Fin p₀.val) → Prop) :
    (∑ r : Fin m → CRTResidues w V,
      uniformPrimeTupleCRTLaw w V r *
        (if E (fun i => r i p₀) then 1 else 0)) =
      uniformUnitTupleProbability p₀.val m E := by
  classical
  let α : CRTPrimeRange w V → Type := fun p => Fin m → Fin p.val
  let μ : ∀ p, α p → ℝ := fun p => uniformUnitTupleMass p.val m
  have hμ (p : CRTPrimeRange w V) : ∑ x : α p, μ p x = 1 := by
    apply uniformUnitTupleMass_total
    exact Nat.Prime.pos ((Finset.mem_filter.mp p.property).2)
  let swap := crtSlotPrimeSwapEquiv (m := m) (w := w) (V := V)
  calc
    _ = ∑ s : ∀ p : CRTPrimeRange w V, α p,
        (∏ p, μ p (s p)) * (if E (s p₀) then 1 else 0) := by
          apply Fintype.sum_equiv swap
          intro r
          rw [uniformPrimeTupleCRTLaw_factor (fun p i => r i p)]
          rfl
    _ = ∑ x : α p₀, μ p₀ x * (if E x then 1 else 0) :=
      piProductMarginal α μ hμ p₀ (fun x => if E x then 1 else 0)
    _ = uniformUnitTupleProbability p₀.val m E := by
      rfl

private def linearFormsTestHeight {m : ℕ}
    (tests : Finset (IntegerPolynomial m)) : ℕ :=
  1 + ∑ Q ∈ tests, (integerPolynomialContent Q + Q.totalDegree)

private theorem linearFormsTestHeight_spec {m : ℕ}
    (tests : Finset (IntegerPolynomial m)) :
    ∀ Q ∈ tests, integerPolynomialContent Q < linearFormsTestHeight tests ∧
      Q.totalDegree ≤ linearFormsTestHeight tests := by
  classical
  intro Q hQ
  have hsingle : integerPolynomialContent Q + Q.totalDegree ≤
      ∑ R ∈ tests, (integerPolynomialContent R + R.totalDegree) :=
    Finset.single_le_sum (f := fun R => integerPolynomialContent R + R.totalDegree)
      (by intro R hR; exact Nat.zero_le _) hQ
  constructor <;> dsimp [linearFormsTestHeight] <;> omega

private theorem uniformCRTTestBad_probability_bound {m w V : ℕ}
    (tests : Finset (IntegerPolynomial m)) (htests : ∀ Q ∈ tests, Q ≠ 0)
    (B : ℕ) (hB : 0 < B)
    (hsize : ∀ Q ∈ tests, integerPolynomialContent Q < B ∧ Q.totalDegree ≤ B)
    (p : CRTPrimeRange w V) :
    (∑ r : Fin m → CRTResidues w V,
      uniformPrimeTupleCRTLaw w V r *
        (if ∃ Q ∈ tests,
          (p.val : ℤ) ∣ evalIntegerPolynomial Q (fun i => ((r i p).val : ℤ)) then 1 else 0)) ≤
      2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / (p.val : ℝ) := by
  classical
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  let E : (Fin m → Fin p.val) → Prop := fun r =>
    ∃ Q ∈ tests, (p.val : ℤ) ∣ evalIntegerPolynomial Q (fun i => (r i).val)
  have hmarg := uniformPrimeTupleCRTLaw_marginal p E
  calc
    _ = uniformUnitTupleProbability p.val m E := by
      simpa [E, Function.comp_apply] using hmarg
    _ ≤ 2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / (p.val : ℝ) :=
      uniformUnitTuple_testBad_probability_bound hp tests htests B hB hsize

private def comparisonPrimeValuationWeight {q b : ℕ} (p : ℕ)
    (a : Fin q → ℕ) : ℝ :=
  ∏ u, (((a u + 1 : ℕ) : ℝ) ^ b / (p : ℝ) ^ (a u))

private theorem comparisonPrimeValuation_regularTerm_le {p q b : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (u v : Fin q) (huv : u ≠ v)
    (hcond : 1 ≤ a v ∧ a v ≤ a u ∧ ∀ w, w ≠ u → a w ≤ a v) :
    comparisonPrimeValuationWeight (b := b) p a *
        ((p : ℝ) ^ ((∑ w, a w) - a u - a v) - 1) ≤
      ((a u + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (a u + a v) := by
  classical
  let total : ℕ := ∑ w, a w
  have hpairSum : a u + a v ≤ total := rowValuationPair_le_sum a u v huv
  have hpowExponent : (∑ w, a w) - a u - a v = total - (a u + a v) := by
    dsimp [total]
    omega
  have htop (w : Fin q) : a w ≤ a u := by
    by_cases hwu : w = u
    · subst w
      exact le_rfl
    · exact (hcond.2.2 w hwu).trans hcond.2.1
  have hpoly :
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) ≤
        ((a u + 1 : ℕ) : ℝ) ^ (b * q) := by
    calc
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) ≤
          ∏ _w : Fin q, ((a u + 1 : ℕ) : ℝ) ^ b := by
            exact finset_prod_le_prod_of_nonneg Finset.univ
              (fun w => ((a w + 1 : ℕ) : ℝ) ^ b)
              (fun _ => ((a u + 1 : ℕ) : ℝ) ^ b)
              (by intro w hw; positivity)
              (by intro w hw; positivity)
              (by
                intro w hw
                gcongr
                exact htop w)
      _ = ((a u + 1 : ℕ) : ℝ) ^ (b * q) := by
            simp [Finset.prod_const, Fintype.card_fin, pow_mul]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpowPos : 0 < (p : ℝ) ^ (total - (a u + a v)) := by positivity
  have hpowOne : (1 : ℝ) ≤ (p : ℝ) ^ (total - (a u + a v)) :=
    one_le_pow₀ (by exact_mod_cast hp.one_le)
  have hpowFactor : (p : ℝ) ^ total =
      (p : ℝ) ^ (a u + a v) * (p : ℝ) ^ (total - (a u + a v)) := by
    have hexp : a u + a v + (total - (a u + a v)) = total := by omega
    calc
      (p : ℝ) ^ total = (p : ℝ) ^ (a u + a v + (total - (a u + a v))) := by rw [hexp]
      _ = (p : ℝ) ^ (a u + a v) * (p : ℝ) ^ (total - (a u + a v)) := by rw [pow_add]
  have hweight : comparisonPrimeValuationWeight (b := b) p a =
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ total := by
    unfold comparisonPrimeValuationWeight
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hcancel :
      ((p : ℝ) ^ (total - (a u + a v)) - 1) / (p : ℝ) ^ total =
        (1 - ((p : ℝ) ^ (total - (a u + a v)))⁻¹) /
          (p : ℝ) ^ (a u + a v) := by
    rw [hpowFactor]
    field_simp [ne_of_gt hpR, ne_of_gt hpowPos]
  have hfactorBound :
      ((p : ℝ) ^ (total - (a u + a v)) - 1) / (p : ℝ) ^ total ≤
        1 / (p : ℝ) ^ (a u + a v) := by
    rw [hcancel]
    have hnonneg : 0 ≤ ((p : ℝ) ^ (total - (a u + a v)))⁻¹ := by positivity
    have hle : 1 - ((p : ℝ) ^ (total - (a u + a v)))⁻¹ ≤ 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  calc
    comparisonPrimeValuationWeight p a *
        ((p : ℝ) ^ ((∑ w, a w) - a u - a v) - 1) =
        (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) *
          (((p : ℝ) ^ (total - (a u + a v)) - 1) / (p : ℝ) ^ total) := by
          rw [hweight, hpowExponent]
          ring
    _ ≤ ((a u + 1 : ℕ) : ℝ) ^ (b * q) /
          (p : ℝ) ^ (a u + a v) := by
          exact (mul_le_mul hpoly hfactorBound (by positivity) (by positivity)).trans_eq
            (by ring)
    _ = ((a u + 1 : ℕ) : ℝ) ^ (b * q) /
          (p : ℝ) ^ (a u + a v) := rfl

private theorem comparisonPrimeValuation_exceptionalTerm_le {p q b : ℕ}
    (hp : p.Prime) (a : Fin q → ℕ) (u : Fin q)
    (hcond : 0 < a u ∧ ∀ v, v ≠ u → a v ≤ a u) :
    comparisonPrimeValuationWeight (b := b) p a *
        ((p : ℝ) ^ ((∑ w, a w) - a u) - 1) ≤
      ((a u + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (a u) := by
  classical
  let total : ℕ := ∑ w, a w
  have hsum : a u ≤ total := rowValuation_le_sum a u
  have htop (w : Fin q) : a w ≤ a u := by
    by_cases hwu : w = u
    · subst w
      exact le_rfl
    · exact hcond.2 w hwu
  have hpoly :
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) ≤
        ((a u + 1 : ℕ) : ℝ) ^ (b * q) := by
    calc
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) ≤
          ∏ _w : Fin q, ((a u + 1 : ℕ) : ℝ) ^ b := by
        exact finset_prod_le_prod_of_nonneg Finset.univ
          (fun w => ((a w + 1 : ℕ) : ℝ) ^ b)
          (fun _ => ((a u + 1 : ℕ) : ℝ) ^ b)
          (by intro w hw; positivity)
          (by intro w hw; positivity)
          (by
            intro w hw
            gcongr
            exact htop w)
      _ = ((a u + 1 : ℕ) : ℝ) ^ (b * q) := by
        simp [Finset.prod_const, Fintype.card_fin, pow_mul]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpowPos : 0 < (p : ℝ) ^ (total - a u) := by positivity
  have hpowOne : (1 : ℝ) ≤ (p : ℝ) ^ (total - a u) :=
    one_le_pow₀ (by exact_mod_cast hp.one_le)
  have hpowFactor : (p : ℝ) ^ total =
      (p : ℝ) ^ (a u) * (p : ℝ) ^ (total - a u) := by
    have hexp : a u + (total - a u) = total := by omega
    calc
      (p : ℝ) ^ total = (p : ℝ) ^ (a u + (total - a u)) := by rw [hexp]
      _ = (p : ℝ) ^ (a u) * (p : ℝ) ^ (total - a u) := by rw [pow_add]
  have hweight : comparisonPrimeValuationWeight (b := b) p a =
      (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ total := by
    unfold comparisonPrimeValuationWeight
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hcancel :
      ((p : ℝ) ^ (total - a u) - 1) / (p : ℝ) ^ total =
        (1 - ((p : ℝ) ^ (total - a u))⁻¹) / (p : ℝ) ^ (a u) := by
    rw [hpowFactor]
    field_simp [ne_of_gt hpR, ne_of_gt hpowPos]
  have hfactorBound :
      ((p : ℝ) ^ (total - a u) - 1) / (p : ℝ) ^ total ≤
        1 / (p : ℝ) ^ (a u) := by
    rw [hcancel]
    have hnonneg : 0 ≤ ((p : ℝ) ^ (total - a u))⁻¹ := by positivity
    have hle : 1 - ((p : ℝ) ^ (total - a u))⁻¹ ≤ 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  calc
    comparisonPrimeValuationWeight (b := b) p a *
        ((p : ℝ) ^ ((∑ w, a w) - a u) - 1) =
        (∏ w : Fin q, ((a w + 1 : ℕ) : ℝ) ^ b) *
          (((p : ℝ) ^ (total - a u) - 1) / (p : ℝ) ^ total) := by
          rw [hweight]
          dsimp [total]
          ring
    _ ≤ ((a u + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (a u) := by
          have htermNonneg :
              0 ≤ ((p : ℝ) ^ (total - a u) - 1) / (p : ℝ) ^ total := by
            apply div_nonneg
            · linarith [hpowOne]
            · positivity
          calc
            _ ≤ ((a u + 1 : ℕ) : ℝ) ^ (b * q) *
                (1 / (p : ℝ) ^ (a u)) :=
              mul_le_mul hpoly hfactorBound htermNonneg (by positivity)
            _ = _ := by ring

private def exceptionalExcessSeriesTerm (p q b A : ℕ) : ℝ :=
  if 1 ≤ A then (((A + 1 : ℕ) : ℝ) ^ (b * q)) / (p : ℝ) ^ A else 0

private theorem exceptionalExcessSeriesTerm_summable (p q b : ℕ) (hp : p.Prime) :
    Summable (fun A : ℕ => exceptionalExcessSeriesTerm p q b A) := by
  let k := b * q
  let t : ℕ → ℝ := fun A => exceptionalExcessSeriesTerm p q b A
  let c : ℕ → ℝ := fun A => (2 / (p : ℝ)) * expPolyWeight k A
  have hF : Summable (fun A : ℕ => expPolyWeight k A) := expPolyWeight_summable k
  have htNonneg : ∀ A, 0 ≤ t A := by
    intro A
    dsimp [t, exceptionalExcessSeriesTerm]
    split_ifs <;> positivity
  have hc : Summable c := by
    simpa [c] using hF.mul_left (2 / (p : ℝ))
  have htc : ∀ A, t A ≤ c A := by
    intro A
    dsimp [t, c, exceptionalExcessSeriesTerm]
    exact exceptionalExpTerm_bound p k A hp
  exact hc.of_nonneg_of_le htNonneg htc

private theorem exceptionalDivisorExcessSeries_range_sum_le {p q b M : ℕ}
    (hp : p.Prime) :
    (∑ A ∈ Finset.range (M + 1), exceptionalExcessSeriesTerm p q b A) ≤
      exceptionalDivisorExcessSeries p q b := by
  have hs : Summable (fun A : ℕ => exceptionalExcessSeriesTerm p q b A) :=
    exceptionalExcessSeriesTerm_summable p q b hp
  have hterm : ∀ A, 0 ≤ exceptionalExcessSeriesTerm p q b A := by
    intro A
    unfold exceptionalExcessSeriesTerm
    split_ifs <;> positivity
  have hseries : exceptionalDivisorExcessSeries p q b =
      ∑' A : ℕ, exceptionalExcessSeriesTerm p q b A := by
    simp [exceptionalDivisorExcessSeries, exceptionalExcessSeriesTerm, Nat.cast_add]
  calc
    _ ≤ ∑' A : ℕ, exceptionalExcessSeriesTerm p q b A :=
      hs.sum_le_tsum _ (by intro A hA; exact hterm A)
    _ = exceptionalDivisorExcessSeries p q b := hseries.symm

private theorem comparisonPrimeValuation_exceptional_cube_sum_le
    {p q b M : ℕ} (hp : p.Prime) (u : Fin q) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1)),
      comparisonPrimeValuationWeight (b := b) p a *
        exceptionalPrimeLocalExcessTerm p a u) ≤
      exceptionalDivisorExcessSeries p q (b + 1) := by
  classical
  let T : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1))
  let indices : Finset ℕ := Finset.range (M + 1)
  let indexOf : (Fin q → ℕ) → ℕ := fun a => a u
  let term : (Fin q → ℕ) → ℝ := fun a =>
    comparisonPrimeValuationWeight (b := b) p a * exceptionalPrimeLocalExcessTerm p a u
  have hMaps : Set.MapsTo indexOf (T : Set (Fin q → ℕ)) (indices : Set ℕ) := by
    intro a ha
    exact Fintype.mem_piFinset.mp ha u
  have hgroup :
      (∑ a ∈ T, term a) =
        ∑ A ∈ indices, ∑ a ∈ T with indexOf a = A, term a := by
    simpa [T, indices, indexOf, term] using
      (Finset.sum_fiberwise_of_maps_to hMaps term).symm
  have hfiber (A : ℕ) (hA : A ∈ indices) :
      (∑ a ∈ T with indexOf a = A, term a) ≤
        exceptionalExcessSeriesTerm p q (b + 1) A := by
    let fiber : Finset (Fin q → ℕ) := T.filter (fun a => indexOf a = A)
    let activePred : (Fin q → ℕ) → Prop := fun a =>
      0 < a u ∧ ∀ v, v ≠ u → a v ≤ a u
    let active : Finset (Fin q → ℕ) := fiber.filter activePred
    let allowed : Finset (Fin q → ℕ) := Fintype.piFinset (fun w : Fin q =>
      if w = u then {A} else Finset.range (A + 1))
    have hsumActive :
        (∑ a ∈ fiber, term a) = ∑ a ∈ active, term a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a ha hnot
      have hfalse : ¬ activePred a := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨ha, h⟩)
      simp [term, activePred, exceptionalPrimeLocalExcessTerm, hfalse]
    have hactiveSubset : active ⊆ allowed := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      have htop := ha'.2
      have hAeq : a u = A := (Finset.mem_filter.mp ha'.1).2
      apply Fintype.mem_piFinset.mpr
      intro w
      by_cases hwu : w = u
      · subst w
        simp [allowed, hAeq]
      · have hwle : a w ≤ A := by rw [← hAeq]; exact htop.2 w hwu
        simp [allowed, hwu, Finset.mem_range]
        omega
    have hcardAllowed : allowed.card ≤ (A + 1) ^ q := by
      have hcardEq : allowed.card =
          ∏ w : Fin q, (if w = u then 1 else A + 1) := by
        change (Fintype.piFinset (fun w : Fin q =>
          if w = u then {A} else Finset.range (A + 1))).card = _
        rw [Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro w hw
        by_cases hwu : w = u
        · simp [hwu]
        · simp [hwu, Finset.card_range]
      calc
        allowed.card = ∏ w : Fin q, (if w = u then 1 else A + 1) := hcardEq
        _ ≤ ∏ _w : Fin q, (A + 1) := by
          apply Finset.prod_le_prod
          intro w hw
          by_cases hwu : w = u
          · simp [hwu]
          · simp [hwu]
        _ = (A + 1) ^ q := by simp [Finset.prod_const, Fintype.card_fin]
    have hpoint (a : Fin q → ℕ) (ha : a ∈ active) :
        term a ≤ ((a u + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (a u) := by
      have ha' := Finset.mem_filter.mp ha
      have htop := ha'.2
      have hAeq : a u = A := (Finset.mem_filter.mp ha'.1).2
      have hcomp := comparisonPrimeValuation_exceptionalTerm_le (b := b) hp a u htop
      change comparisonPrimeValuationWeight (b := b) p a *
        exceptionalPrimeLocalExcessTerm p a u ≤
          ((a u + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (a u)
      unfold exceptionalPrimeLocalExcessTerm
      rw [if_pos htop]
      exact hcomp
    have hpointSeries (a : Fin q → ℕ) (ha : a ∈ active) :
        term a ≤ ((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A := by
      have hAeq : a u = A := by
        simpa [indexOf] using (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      have hpoint' := hpoint a ha
      rw [hAeq] at hpoint'
      exact hpoint'
    have hsmallNonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A := by positivity
    by_cases hApos : 1 ≤ A
    · calc
        (∑ a ∈ fiber, term a) = ∑ a ∈ active, term a := hsumActive
        _ ≤ ∑ _a ∈ active, ((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A := by
          apply Finset.sum_le_sum
          intro a ha
          exact hpointSeries a ha
        _ = (active.card : ℝ) * (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A) := by
          simp [Finset.sum_const]
        _ ≤ (allowed.card : ℝ) * (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A) := by
          have hcard : (active.card : ℝ) ≤ (allowed.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hactiveSubset
          exact mul_le_mul_of_nonneg_right hcard hsmallNonneg
        _ ≤ ((A + 1 : ℕ) : ℝ) ^ q * (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A) := by
          have hcard : (allowed.card : ℝ) ≤ ((A + 1 : ℕ) : ℝ) ^ q := by
            exact_mod_cast hcardAllowed
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = exceptionalExcessSeriesTerm p q (b + 1) A := by
          unfold exceptionalExcessSeriesTerm
          rw [if_pos hApos]
          calc
            ((A + 1 : ℕ) : ℝ) ^ q * (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ A) =
                (((A + 1 : ℕ) : ℝ) ^ q * ((A + 1 : ℕ) : ℝ) ^ (b * q)) /
                  (p : ℝ) ^ A := by ring
            _ = ((A + 1 : ℕ) : ℝ) ^ (q + b * q) / (p : ℝ) ^ A := by
                  rw [← pow_add]
            _ = ((A + 1 : ℕ) : ℝ) ^ ((b + 1) * q) / (p : ℝ) ^ A := by
                  congr 2
                  ring
    · have hA0 : A = 0 := by omega
      have hempty : active = ∅ := by
        ext a
        constructor
        · intro ha
          have ha' := Finset.mem_filter.mp ha
          have hAeq : a u = A := (Finset.mem_filter.mp ha'.1).2
          have hpos := ha'.2.1
          omega
        · intro ha
          simp at ha
      rw [hsumActive, hempty]
      simp [exceptionalExcessSeriesTerm, hA0]
  calc
    (∑ a ∈ T, term a) = ∑ A ∈ indices, ∑ a ∈ T with indexOf a = A, term a := hgroup
    _ ≤ ∑ A ∈ indices, exceptionalExcessSeriesTerm p q (b + 1) A := by
      apply Finset.sum_le_sum
      intro A hA
      exact hfiber A hA
    _ ≤ exceptionalDivisorExcessSeries p q (b + 1) :=
      exceptionalDivisorExcessSeries_range_sum_le hp

private def regularExcessSeriesTerm (p q b A B : ℕ) : ℝ :=
  if 1 ≤ B ∧ B ≤ A then
    (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ (b * q) / (p : ℝ) ^ (A + B)
  else 0

private theorem regularExcessSeriesTerm_summable (p q b : ℕ) (hp : p.Prime) :
    Summable (fun x : ℕ × ℕ => regularExcessSeriesTerm p q b x.1 x.2) := by
  let k := b * q
  let F : ℝ := ∑' A : ℕ, expPolyWeight k A
  let G : ℝ := ∑' x : ℕ × ℕ, expPolyWeight k x.1 * expPolyWeight k x.2
  have hF : Summable (fun A : ℕ => expPolyWeight k A) := expPolyWeight_summable k
  have hFnonneg : ∀ A, 0 ≤ expPolyWeight k A := by
    intro A
    unfold expPolyWeight
    positivity
  have hpair : Summable
      (fun x : ℕ × ℕ => expPolyWeight k x.1 * expPolyWeight k x.2) :=
    hF.mul_of_nonneg hF hFnonneg hFnonneg
  let t : ℕ × ℕ → ℝ := fun x => regularExcessSeriesTerm p q b x.1 x.2
  let c : ℕ × ℕ → ℝ := fun x =>
    (4 / (p : ℝ) ^ 2) * expPolyWeight k x.1 * expPolyWeight k x.2
  have htNonneg : ∀ x, 0 ≤ t x := by
    intro x
    dsimp [t, regularExcessSeriesTerm]
    split_ifs <;> positivity
  have hc : Summable c := by
    simpa [c, G, mul_assoc] using hpair.mul_left (4 / (p : ℝ) ^ 2)
  have htle : ∀ x, t x ≤ c x := by
    intro x
    dsimp [t, c, regularExcessSeriesTerm]
    exact regularExpTerm_bound p k x.1 x.2 hp
  exact hc.of_nonneg_of_le htNonneg htle

private theorem regularDivisorExcessSeries_range_sum_le {p q b M : ℕ}
    (hp : p.Prime) :
    (∑ A ∈ Finset.range (M + 1), ∑ B ∈ Finset.range (M + 1),
      regularExcessSeriesTerm p q b A B) ≤ regularDivisorExcessSeries p q b := by
  classical
  have ht : Summable (fun x : ℕ × ℕ => regularExcessSeriesTerm p q b x.1 x.2) :=
    regularExcessSeriesTerm_summable p q b hp
  have hseries : regularDivisorExcessSeries p q b =
      ∑' x : ℕ × ℕ, regularExcessSeriesTerm p q b x.1 x.2 := by
    simpa [regularDivisorExcessSeries, regularExcessSeriesTerm] using ht.tsum_prod.symm
  have hnonneg (x : ℕ × ℕ) : 0 ≤ regularExcessSeriesTerm p q b x.1 x.2 := by
    unfold regularExcessSeriesTerm
    split_ifs <;> positivity
  have hsum :
      (∑ A ∈ Finset.range (M + 1), ∑ B ∈ Finset.range (M + 1),
        regularExcessSeriesTerm p q b A B) =
        ∑ x ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
          regularExcessSeriesTerm p q b x.1 x.2 := by
    rw [Finset.sum_product]
  calc
    _ = ∑ x ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        regularExcessSeriesTerm p q b x.1 x.2 := hsum
    _ ≤ ∑' x : ℕ × ℕ, regularExcessSeriesTerm p q b x.1 x.2 :=
      ht.sum_le_tsum _ (by intro x hx; exact hnonneg x)
    _ = regularDivisorExcessSeries p q b := hseries.symm

private theorem comparisonPrimeValuation_regularTerm_cube_sum_le
    {p q b M : ℕ} (hp : p.Prime) (u v : Fin q) (huv : u ≠ v) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1)),
      comparisonPrimeValuationWeight (b := b) p a *
        regularPrimeLocalExcessTerm p a u v) ≤
      regularDivisorExcessSeries p q (b + 1) := by
  classical
  let T : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1))
  let Pairs : Finset (ℕ × ℕ) := Finset.range (M + 1) ×ˢ Finset.range (M + 1)
  let pairOf : (Fin q → ℕ) → ℕ × ℕ := fun a => (a u, a v)
  let term : (Fin q → ℕ) → ℝ := fun a =>
    comparisonPrimeValuationWeight (b := b) p a * regularPrimeLocalExcessTerm p a u v
  have hMaps : Set.MapsTo pairOf (T : Set (Fin q → ℕ)) (Pairs : Set (ℕ × ℕ)) := by
    intro a ha
    have haT := Fintype.mem_piFinset.mp ha
    apply Finset.mem_product.mpr
    exact ⟨haT u, haT v⟩
  have hgroup :
      (∑ a ∈ T, term a) =
        ∑ AB ∈ Pairs, ∑ a ∈ T with pairOf a = AB, term a := by
    simpa [T, Pairs, pairOf, term] using
      (Finset.sum_fiberwise_of_maps_to hMaps term).symm
  have hfiber (AB : ℕ × ℕ) (hABmem : AB ∈ Pairs) :
      (∑ a ∈ T with pairOf a = AB, term a) ≤
        regularExcessSeriesTerm p q (b + 1) AB.1 AB.2 := by
    let A := AB.1
    let B := AB.2
    have hAmax : A ≤ M := by
      have h := Finset.mem_product.mp hABmem |>.1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp h)
    have hBmax : B ≤ M := by
      have h := Finset.mem_product.mp hABmem |>.2
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp h)
    by_cases hAB : 1 ≤ B ∧ B ≤ A
    · let activePred : (Fin q → ℕ) → Prop := fun a =>
        u ≠ v ∧ 0 < a u ∧ 0 < a v ∧ a v ≤ a u ∧
          ∀ w, w ≠ u → a w ≤ a v
      let fiber : Finset (Fin q → ℕ) := T.filter (fun a => pairOf a = AB)
      let active : Finset (Fin q → ℕ) := fiber.filter activePred
      let allowed : Finset (Fin q → ℕ) := Fintype.piFinset (fun w : Fin q =>
        if w = u then {A} else Finset.range (B + 1))
      have hsumActive :
          (∑ a ∈ fiber, term a) = ∑ a ∈ active, term a := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hnot
        have hfalse : ¬ activePred a := by
          intro h
          exact hnot (Finset.mem_filter.mpr ⟨ha, h⟩)
        simp [term, activePred, regularPrimeLocalExcessTerm, hfalse]
      have hactiveSubset : active ⊆ allowed := by
        intro a ha
        have ha' := Finset.mem_filter.mp ha
        have htop := ha'.2
        have hpPair := (Finset.mem_filter.mp ha'.1).2
        have hau : a u = A := congrArg Prod.fst (by simpa [pairOf, A, B] using hpPair)
        have hav : a v = B := congrArg Prod.snd (by simpa [pairOf, A, B] using hpPair)
        apply Fintype.mem_piFinset.mpr
        intro w
        by_cases hwu : w = u
        · subst w
          simp [allowed, hau]
        · have hwle : a w ≤ B := by
            rw [← hav]
            exact htop.2.2.2.2 w hwu
          simp [allowed, hwu, Finset.mem_range]
          omega
      have hcardAllowed : allowed.card ≤ (B + 1) ^ q := by
        have hcardEq : allowed.card =
            ∏ w : Fin q, (if w = u then 1 else B + 1) := by
          change (Fintype.piFinset (fun w : Fin q =>
            if w = u then {A} else Finset.range (B + 1))).card = _
          rw [Fintype.card_piFinset]
          apply Finset.prod_congr rfl
          intro w hw
          by_cases hwu : w = u
          · simp [hwu]
          · simp [hwu, Finset.card_range]
        calc
          allowed.card = ∏ w : Fin q, (if w = u then 1 else B + 1) := hcardEq
          _ ≤ ∏ _w : Fin q, (B + 1) := by
            apply Finset.prod_le_prod
            intro w hw
            by_cases hwu : w = u
            · simp [hwu]
            · simp [hwu]
          _ = (B + 1) ^ q := by simp [Finset.prod_const, Fintype.card_fin]
      have hpoint (a : Fin q → ℕ) (ha : a ∈ active) :
          term a ≤ ((a u + 1 : ℕ) : ℝ) ^ (b * q) /
            (p : ℝ) ^ (a u + a v) := by
        have ha' := Finset.mem_filter.mp ha
        have htop := ha'.2
        have hpPair := (Finset.mem_filter.mp ha'.1).2
        have hau : a u = A := congrArg Prod.fst (by simpa [pairOf, A, B] using hpPair)
        have hav : a v = B := congrArg Prod.snd (by simpa [pairOf, A, B] using hpPair)
        have hcond : 1 ≤ a v ∧ a v ≤ a u ∧ ∀ w, w ≠ u → a w ≤ a v := by
          refine ⟨?_, ?_, ?_⟩
          · simpa [hav] using hAB.1
          · simpa [hau, hav] using hAB.2
          · intro w hwu
            exact htop.2.2.2.2 w hwu
        have hterm : regularPrimeLocalExcessTerm p a u v =
            (p : ℝ) ^ ((∑ w, a w) - a u - a v) - 1 := by
          have huPos : 0 < a u := by omega
          have hvPos : 0 < a v := by omega
          have hcondFull : u ≠ v ∧ 0 < a u ∧ 0 < a v ∧ a v ≤ a u ∧
              (∀ w, w ≠ u → a w ≤ a v) :=
            ⟨huv, huPos, hvPos, hcond.2.1, hcond.2.2⟩
          unfold regularPrimeLocalExcessTerm
          rw [if_pos hcondFull]
        have hcomp := comparisonPrimeValuation_regularTerm_le (b := b) hp a u v huv hcond
        change comparisonPrimeValuationWeight (b := b) p a *
          regularPrimeLocalExcessTerm p a u v ≤ _
        rw [hterm]
        simpa [hau, hav] using hcomp
      have hpointSeries (a : Fin q → ℕ) (ha : a ∈ active) :
          term a ≤ ((A + 1 : ℕ) : ℝ) ^ (b * q) /
            (p : ℝ) ^ (A + B) := by
        have ha' := Finset.mem_filter.mp ha
        have hpPair := (Finset.mem_filter.mp ha'.1).2
        have hau : a u = A := congrArg Prod.fst (by simpa [pairOf, A, B] using hpPair)
        have hav : a v = B := congrArg Prod.snd (by simpa [pairOf, A, B] using hpPair)
        simpa [hau, hav] using hpoint a ha
      have hscalarNonneg :
          0 ≤ ((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (A + B) := by positivity
      calc
        (∑ a ∈ fiber, term a) = ∑ a ∈ active, term a := hsumActive
        _ ≤ ∑ _a ∈ active,
              ((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (A + B) := by
              apply Finset.sum_le_sum
              intro a ha
              exact hpointSeries a ha
        _ = (active.card : ℝ) *
              (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (A + B)) := by
                simp [Finset.sum_const]
        _ ≤ (allowed.card : ℝ) *
              (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (A + B)) := by
              have hcard : (active.card : ℝ) ≤ (allowed.card : ℝ) := by
                exact_mod_cast Finset.card_le_card hactiveSubset
              exact mul_le_mul_of_nonneg_right hcard hscalarNonneg
        _ ≤ ((B + 1 : ℕ) : ℝ) ^ q *
              (((A + 1 : ℕ) : ℝ) ^ (b * q) / (p : ℝ) ^ (A + B)) := by
              have hcard : (allowed.card : ℝ) ≤ ((B + 1 : ℕ) : ℝ) ^ q := by
                exact_mod_cast hcardAllowed
              exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ regularExcessSeriesTerm p q (b + 1) A B := by
              rw [regularExcessSeriesTerm, if_pos hAB]
              have hAreal : (1 : ℝ) ≤ ((A + 1 : ℕ) : ℝ) := by
                simpa [Nat.cast_add] using (show (1 : ℝ) ≤ (A : ℝ) + 1 by positivity)
              have hBreal : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
                simpa [Nat.cast_add] using (show (1 : ℝ) ≤ (B : ℝ) + 1 by positivity)
              have hqle : q ≤ (b + 1) * q := by
                simpa using Nat.mul_le_mul_right q (Nat.succ_le_succ (Nat.zero_le b))
              have hbqle : b * q ≤ (b + 1) * q :=
                Nat.mul_le_mul_right q (Nat.le_succ b)
              have hnum : ((B + 1 : ℕ) : ℝ) ^ q *
                    ((A + 1 : ℕ) : ℝ) ^ (b * q) ≤
                  (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ ((b + 1) * q) := by
                calc
                  _ ≤ ((B + 1 : ℕ) : ℝ) ^ ((b + 1) * q) *
                      ((A + 1 : ℕ) : ℝ) ^ ((b + 1) * q) := by
                        exact mul_le_mul
                          (pow_le_pow_right₀ hBreal hqle)
                          (pow_le_pow_right₀ hAreal hbqle) (by positivity) (by positivity)
                  _ = _ := by
                    rw [mul_pow]
                    simp only [Nat.cast_add, Nat.cast_one]
                    ring
              calc
                _ = ((((B + 1 : ℕ) : ℝ) ^ q) *
                    ((A + 1 : ℕ) : ℝ) ^ (b * q)) / (p : ℝ) ^ (A + B) := by ring
                _ ≤ (((A + 1 : ℕ) : ℝ) * (B + 1 : ℝ)) ^ ((b + 1) * q) /
                    (p : ℝ) ^ (A + B) :=
                  div_le_div_of_nonneg_right hnum (by positivity)
    · let fiber : Finset (Fin q → ℕ) := T.filter (fun a => pairOf a = AB)
      have hzero (a : Fin q → ℕ) (ha : a ∈ fiber) : term a = 0 := by
        have hpPair := (Finset.mem_filter.mp ha).2
        unfold term regularPrimeLocalExcessTerm
        split_ifs with hcond
        · have hau : a u = A := congrArg Prod.fst (by simpa [pairOf, A, B] using hpPair)
          have hav : a v = B := congrArg Prod.snd (by simpa [pairOf, A, B] using hpPair)
          rcases hcond with ⟨_, hAu, hAv, hBA, _⟩
          have hBpos : 1 ≤ B := by simpa [hav] using (Nat.succ_le_of_lt hAv)
          have hBA' : B ≤ A := by simpa [hau, hav] using hBA
          exact False.elim (hAB ⟨hBpos, hBA'⟩)
        · simp [hcond]
      rw [Finset.sum_eq_zero hzero]
      simp [regularExcessSeriesTerm, A, B, hAB]
  calc
    (∑ a ∈ T, term a) =
        ∑ AB ∈ Pairs, ∑ a ∈ T with pairOf a = AB, term a := hgroup
    _ ≤ ∑ AB ∈ Pairs, regularExcessSeriesTerm p q (b + 1) AB.1 AB.2 := by
          apply Finset.sum_le_sum
          intro AB hAB
          exact hfiber AB hAB
    _ = ∑ A ∈ Finset.range (M + 1), ∑ B ∈ Finset.range (M + 1),
          regularExcessSeriesTerm p q (b + 1) A B := by
          simp [Pairs, Finset.sum_product]
    _ ≤ regularDivisorExcessSeries p q (b + 1) :=
          regularDivisorExcessSeries_range_sum_le hp

private theorem comparisonPrimeValuation_regular_cube_sum_le
    {p q b M : ℕ} (hp : p.Prime) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1)),
      comparisonPrimeValuationWeight (b := b) p a * regularPrimeLocalExcess p a) ≤
      (q : ℝ) ^ 2 * regularDivisorExcessSeries p q (b + 1) := by
  classical
  let T : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1))
  have hswap :
      (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        regularPrimeLocalExcess p a) =
      ∑ u : Fin q, ∑ v : Fin q, ∑ a ∈ T,
        comparisonPrimeValuationWeight (b := b) p a *
          regularPrimeLocalExcessTerm p a u v := by
    simp only [regularPrimeLocalExcess, Finset.mul_sum]
    calc
      _ = ∑ u : Fin q, ∑ a ∈ T, ∑ v : Fin q,
          comparisonPrimeValuationWeight (b := b) p a *
            regularPrimeLocalExcessTerm p a u v := by
              rw [Finset.sum_comm (s := T) (t := Finset.univ)]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro u hu
            exact Finset.sum_comm (s := T) (t := Finset.univ)
  have hseries : 0 ≤ regularDivisorExcessSeries p q (b + 1) := by
    unfold regularDivisorExcessSeries
    apply tsum_nonneg
    intro A
    apply tsum_nonneg
    intro B
    split_ifs <;> positivity
  calc
    (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        regularPrimeLocalExcess p a) =
      ∑ u : Fin q, ∑ v : Fin q, ∑ a ∈ T,
        comparisonPrimeValuationWeight (b := b) p a *
          regularPrimeLocalExcessTerm p a u v := hswap
    _ ≤ ∑ u : Fin q, ∑ v : Fin q,
        regularDivisorExcessSeries p q (b + 1) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      by_cases huv : u = v
      · subst v
        have hzero :
            (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
              regularPrimeLocalExcessTerm p a u u) = 0 := by
          simp [regularPrimeLocalExcessTerm]
        rw [hzero]
        exact hseries
      · exact comparisonPrimeValuation_regularTerm_cube_sum_le hp u v huv
    _ = (q : ℝ) ^ 2 * regularDivisorExcessSeries p q (b + 1) := by
      simp [Finset.sum_const, Fintype.card_fin]
      ring

private theorem comparisonPrimeValuation_exceptional_local_cube_sum_le
    {p q b M : ℕ} (hp : p.Prime) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1)),
      comparisonPrimeValuationWeight (b := b) p a * exceptionalPrimeLocalExcess p a) ≤
      (q : ℝ) * exceptionalDivisorExcessSeries p q (b + 1) := by
  classical
  let T : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1))
  have hswap :
      (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        exceptionalPrimeLocalExcess p a) =
      ∑ u : Fin q, ∑ a ∈ T,
        comparisonPrimeValuationWeight (b := b) p a *
          exceptionalPrimeLocalExcessTerm p a u := by
    simp only [exceptionalPrimeLocalExcess, Finset.mul_sum]
    rw [Finset.sum_comm (s := T) (t := Finset.univ)]
  calc
    (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        exceptionalPrimeLocalExcess p a) =
      ∑ u : Fin q, ∑ a ∈ T,
        comparisonPrimeValuationWeight (b := b) p a *
          exceptionalPrimeLocalExcessTerm p a u := hswap
    _ ≤ ∑ u : Fin q, exceptionalDivisorExcessSeries p q (b + 1) := by
      apply Finset.sum_le_sum
      intro u hu
      exact comparisonPrimeValuation_exceptional_cube_sum_le hp u
    _ = (q : ℝ) * exceptionalDivisorExcessSeries p q (b + 1) := by
      simp [Finset.sum_const, Fintype.card_fin]

private def averagedLocalBeta {q : ℕ} (H : ℝ) (p : ℕ)
    (a : Fin q → ℕ) : ℝ :=
  regularPrimeLocalExcess p a + H / (p : ℝ) * exceptionalPrimeLocalExcess p a

private theorem averagedLocalBeta_box {p q b M : ℕ} (hp : p.Prime)
    (H : ℝ) (hH : 0 ≤ H) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1)),
      comparisonPrimeValuationWeight (b := b) p a * averagedLocalBeta H p a) ≤
      (q : ℝ) ^ 2 * regularDivisorExcessSeries p q (b + 1) +
        H * q * (exceptionalDivisorExcessSeries p q (b + 1) / p) := by
  classical
  let T : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (M + 1))
  have hreg := comparisonPrimeValuation_regular_cube_sum_le
    (b := b) (q := q) (M := M) hp
  have hex := comparisonPrimeValuation_exceptional_local_cube_sum_le
    (b := b) (q := q) (M := M) hp
  have hfactor :
      (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        (H / (p : ℝ) * exceptionalPrimeLocalExcess p a)) =
      H / (p : ℝ) *
        (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
          exceptionalPrimeLocalExcess p a) := by
    calc
      _ = ∑ a ∈ T, (H / (p : ℝ)) *
          (comparisonPrimeValuationWeight (b := b) p a *
            exceptionalPrimeLocalExcess p a) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = _ := by rw [← Finset.mul_sum]
  have hexScaled :
      (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
        (H / (p : ℝ) * exceptionalPrimeLocalExcess p a)) ≤
      H * q * (exceptionalDivisorExcessSeries p q (b + 1) / p) := by
    rw [hfactor]
    have hcoef : 0 ≤ H / (p : ℝ) := div_nonneg hH (by positivity)
    calc
      H / (p : ℝ) *
          (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
            exceptionalPrimeLocalExcess p a) ≤
        H / (p : ℝ) * ((q : ℝ) * exceptionalDivisorExcessSeries p q (b + 1)) :=
          mul_le_mul_of_nonneg_left (by simpa [T] using hex) hcoef
      _ = H * q * (exceptionalDivisorExcessSeries p q (b + 1) / p) := by ring
  change (∑ a ∈ T, comparisonPrimeValuationWeight (b := b) p a *
      (regularPrimeLocalExcess p a + H / (p : ℝ) * exceptionalPrimeLocalExcess p a)) ≤ _
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  exact add_le_add (by simpa [T] using hreg) hexScaled

private theorem harmonicProductLaw_ne_zero_of_mem_support {k : ℕ} (W : ℕ)
    (X : Fin k → ℕ) (hX : ∀ i, 0 < X i)
    (hH : ∀ i, 0 < harmonicNormalizer (X i) W)
    (σ : ℕ) (hσ : σ ∈ harmonicProductSupport W X) :
    harmonicProductLaw W X σ ≠ 0 := by
  classical
  let S : Fin k → Finset ℕ := fun i => harmonicNatSupport (X i) W
  let T : Finset (Fin k → ℕ) := Fintype.piFinset S
  let f : (Fin k → ℕ) → ℝ := fun t =>
    (if (∏ i, t i) = σ then 1 else 0) * ∏ i, harmonicNatLaw (X i) W (t i)
  change σ ∈ (Fintype.piFinset S).image (fun t => ∏ i, t i) at hσ
  rcases Finset.mem_image.mp hσ with
    ⟨t, ht, hprod⟩
  have hrawNonneg (i : Fin k) (n : ℕ) : 0 ≤ harmonicNatLaw (X i) W n := by
    unfold harmonicNatLaw
    split_ifs with h
    · exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (hH i).le)
    · norm_num
  have hfNonneg (t : Fin k → ℕ) : 0 ≤ f t := by
    dsimp [f]
    exact mul_nonneg (by split_ifs <;> norm_num)
      (Finset.prod_nonneg fun i hi => hrawNonneg i (t i))
  have htermzero (t : Fin k → ℕ) (ht : t ∉ T) : f t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hzero := harmonicNatLaw_zero_of_not_mem (X i) W (t i) (by simpa [S] using hi)
    have hweightzero :
        (∏ j, harmonicNatLaw (X j) W (t j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    dsimp [f]
    rw [hweightzero]
    simp
  have hrawPos (i : Fin k) : 0 < harmonicNatLaw (X i) W (t i) := by
    have hmem : t i ∈ harmonicNatSupport (X i) W := by
      simpa [S] using Fintype.mem_piFinset.mp ht i
    have hmem' := Finset.mem_filter.mp hmem
    have hrange := Finset.mem_Ico.mp hmem'.1
    have hcond : X i ≤ t i ∧ t i < (X i) ^ 2 ∧ Nat.Coprime (t i) W :=
      ⟨hrange.1, hrange.2, hmem'.2⟩
    unfold harmonicNatLaw
    rw [if_pos hcond]
    have hn : 0 < (t i : ℝ) := by exact_mod_cast lt_of_lt_of_le (hX i) hrange.1
    exact one_div_pos.mpr (mul_pos hn (hH i))
  have hprodPos : 0 < ∏ i, harmonicNatLaw (X i) W (t i) :=
    Finset.prod_pos fun i hi => hrawPos i
  have hft : 0 < f t := by
    dsimp [f]
    rw [if_pos hprod]
    simpa using hprodPos
  have hsumPos : 0 < ∑ t ∈ T, f t :=
    lt_of_lt_of_le hft (Finset.single_le_sum (f := f)
      (fun s hs => hfNonneg s) ht)
  unfold harmonicProductLaw
  rw [tsum_eq_sum (s := T) htermzero]
  exact ne_of_gt hsumPos

private def linearFormsDivisorTupleSupport {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) (N : ℕ) :
    Finset (Fin q → ℕ) :=
  Fintype.piFinset (fun u => harmonicProductSupport (primorial (N + 1))
    (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)))

private def linearFormsDivisorTupleMass {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ) (σ : Fin q → ℕ) : ℝ :=
  ∏ u, divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u)

private def linearFormsPrimeSet {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) (N : ℕ) : Finset ℕ :=
  (Finset.Ioc (N + 1) (D.V N + 1)).filter Nat.Prime

private def linearFormsValVector {q : ℕ} (σ : Fin q → ℕ) (p : ℕ) : Fin q → ℕ :=
  fun u => Nat.factorization (σ u) p

private theorem linearFormsDivisorTuple_support_facts {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) (N : ℕ) :
    (∀ σ, 0 ≤ linearFormsDivisorTupleMass D N σ) ∧
    (∑ σ ∈ linearFormsDivisorTupleSupport D N,
      linearFormsDivisorTupleMass D N σ) = 1 ∧
    (∀ σ, σ ∉ linearFormsDivisorTupleSupport D N →
      linearFormsDivisorTupleMass D N σ = 0) ∧
    (∀ σ ∈ linearFormsDivisorTupleSupport D N, ∀ u,
      1 ≤ σ u ∧ σ u ≤ D.V N ∧ Nat.Coprime (σ u) (primorial (N + 1))) := by
  classical
  let W : ℕ := primorial (N + 1)
  let rowSupport : Fin q → Finset ℕ := fun u =>
    harmonicProductSupport W
      (fun j => S.core.parameters.X N ((D.divisor u).cutoff j))
  have hrowNonneg (u : Fin q) (σ : ℕ) :
      0 ≤ divisorTemplateLaw S.core.parameters N (D.divisor u) σ :=
    (divisorTemplateLaw_probability D N u).1 σ
  have hrowZero (u : Fin q) (σ : ℕ) (hσ : σ ∉ rowSupport u) :
      divisorTemplateLaw S.core.parameters N (D.divisor u) σ = 0 := by
    change harmonicProductLaw W
      (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)) σ = 0
    exact harmonicProductLaw_zero_of_not_mem_support W _ σ (by simpa [rowSupport] using hσ)
  have hrowSum (u : Fin q) :
      ∑ σ ∈ rowSupport u, divisorTemplateLaw S.core.parameters N (D.divisor u) σ = 1 := by
    have htotal := (divisorTemplateLaw_probability D N u).2
    rw [tsum_eq_sum (s := rowSupport u) (by
      intro σ hσ
      exact hrowZero u σ hσ)] at htotal
    exact htotal
  have htupleSum :
      (∑ σ ∈ linearFormsDivisorTupleSupport D N,
        linearFormsDivisorTupleMass D N σ) = 1 := by
    calc
      _ = ∏ u : Fin q, ∑ σ ∈ rowSupport u,
          divisorTemplateLaw S.core.parameters N (D.divisor u) σ := by
        simpa [linearFormsDivisorTupleSupport, linearFormsDivisorTupleMass,
          rowSupport, W] using
          (Finset.prod_univ_sum rowSupport
            (fun u σ => divisorTemplateLaw S.core.parameters N (D.divisor u) σ)).symm
      _ = 1 := by simp [hrowSum]
  have htupleZero (σ : Fin q → ℕ)
      (hσ : σ ∉ linearFormsDivisorTupleSupport D N) :
      linearFormsDivisorTupleMass D N σ = 0 := by
    have hnot : ¬ ∀ u, σ u ∈ rowSupport u := by
      intro hall
      exact hσ (Fintype.mem_piFinset.mpr hall)
    obtain ⟨u, hu⟩ := not_forall.mp hnot
    unfold linearFormsDivisorTupleMass
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    exact hrowZero u (σ u) (by simpa [rowSupport, W] using hu)
  have htupleBound (σ : Fin q → ℕ)
      (hσ : σ ∈ linearFormsDivisorTupleSupport D N) (u : Fin q) :
      1 ≤ σ u ∧ σ u ≤ D.V N ∧ Nat.Coprime (σ u) W := by
    have hrow : σ u ∈ rowSupport u := Fintype.mem_piFinset.mp hσ u
    have hX (j : Fin (D.divisor u).arity) :
        0 < S.core.parameters.X N ((D.divisor u).cutoff j) :=
      S.core.parameters.Xpos N ((D.divisor u).cutoff j)
    have hW : 0 < W := by dsimp [W]; exact primorial_pos _
    have hH (j : Fin (D.divisor u).arity) :
        0 < harmonicNormalizer
          (S.core.parameters.X N ((D.divisor u).cutoff j)) W := by
      apply harmonicNormalizer_pos_of_cutoff _ W hW
      exact S.gapStage.valid_raw_cutoffs N ((D.divisor u).cutoff j)
    have hLaw : divisorTemplateLaw S.core.parameters N (D.divisor u) (σ u) ≠ 0 := by
      change harmonicProductLaw W
        (fun j => S.core.parameters.X N ((D.divisor u).cutoff j)) (σ u) ≠ 0
      exact harmonicProductLaw_ne_zero_of_mem_support W _ hX hH (σ u)
        (by simpa [rowSupport] using hrow)
    exact ⟨D.divisor_positive N u (σ u) hLaw,
      D.divisor_bounded N u (σ u) hLaw,
      divisorTemplateLaw_coprime_primorial D N u (σ u) hLaw⟩
  refine ⟨?_, htupleSum, htupleZero, ?_⟩
  · intro σ
    unfold linearFormsDivisorTupleMass
    apply Finset.prod_nonneg
    intro u hu
    exact hrowNonneg u (σ u)
  · intro σ hσ u
    simpa [W] using htupleBound σ hσ u

private theorem averagedLocalBeta_prime_square_bound {q b m : ℕ}
    (tests : Finset (IntegerPolynomial m)) (B : ℕ) (hB : 0 < B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ p : ℕ, p.Prime → ∀ L : ℕ,
      (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (L + 1)),
        comparisonPrimeValuationWeight (b := b) p a *
          averagedLocalBeta
            (2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ)) p a) ≤ C₁ / (p : ℝ) ^ 2 := by
  let H : ℝ := 2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  obtain ⟨C₂, hC₂, hseries⟩ := local_divisor_excess_prime_square_bound q (b + 1)
  let C₁ : ℝ := ((q : ℝ) ^ 2 + H * q + 1) * C₂
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    positivity
  refine ⟨C₁, hC₁, ?_⟩
  intro p hp L
  have hbox := averagedLocalBeta_box (b := b) (q := q) (M := L) hp H hH
  obtain ⟨hreg, hex⟩ := hseries p hp
  have hcoeff : (q : ℝ) ^ 2 * C₂ + H * q * C₂ ≤
      ((q : ℝ) ^ 2 + H * q + 1) * C₂ := by
    have hfactor : (q : ℝ) ^ 2 * C₂ + H * q * C₂ =
        ((q : ℝ) ^ 2 + H * q) * C₂ := by ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right (by linarith) hC₂.le
  calc
    _ ≤ (q : ℝ) ^ 2 * regularDivisorExcessSeries p q (b + 1) +
        H * q * (exceptionalDivisorExcessSeries p q (b + 1) / p) := hbox
    _ ≤ (q : ℝ) ^ 2 * (C₂ / (p : ℝ) ^ 2) + H * q * (C₂ / (p : ℝ) ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hreg (by positivity))
        (mul_le_mul_of_nonneg_left hex (by positivity))
    _ = ((q : ℝ) ^ 2 * C₂ + H * q * C₂) / (p : ℝ) ^ 2 := by ring
    _ ≤ (((q : ℝ) ^ 2 + H * q + 1) * C₂) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcoeff (by positivity)
    _ = C₁ / (p : ℝ) ^ 2 := by rfl

namespace LinearFormsAux

theorem finite_joint_product_excess {α ι : Type*} [Fintype α] [DecidableEq ι]
    (P : Finset ι) (mass : α → ℝ) (beta : α → ι → ℝ)
    (C : ℝ) (c : ι → ℝ)
    (hjoint : ∀ T ∈ P.powerset.erase ∅,
      (∑ x, mass x * ∏ p ∈ T, beta x p) ≤ C * ∏ p ∈ T, c p) :
    (∑ x, mass x * ((∏ p ∈ P, (1 + beta x p)) - 1)) ≤
      C * ((∏ p ∈ P, (1 + c p)) - 1) := by
  classical
  have hexpand (f : ι → ℝ) :
      (∏ p ∈ P, (1 + f p)) - 1 =
        ∑ T ∈ P.powerset.erase ∅, ∏ p ∈ T, f p := by
    have h := Finset.prod_add_one (f := f) P
    have hsum : (∑ T ∈ P.powerset, ∏ p ∈ T, f p) =
        1 + ∑ T ∈ P.powerset.erase ∅, ∏ p ∈ T, f p := by
      rw [← Finset.add_sum_erase P.powerset (fun T => ∏ p ∈ T, f p)
        (by simp : ∅ ∈ P.powerset)]
      simp
    have hprod : (∏ p ∈ P, (1 + f p)) = (∏ p ∈ P, (f p + 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring
    rw [hprod, h, hsum]
    ring
  calc
    _ = ∑ T ∈ P.powerset.erase ∅, ∑ x, mass x * ∏ p ∈ T, beta x p := by
      simp_rw [hexpand, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ T ∈ P.powerset.erase ∅, C * ∏ p ∈ T, c p :=
      Finset.sum_le_sum (fun T hT => hjoint T hT)
    _ = C * ((∏ p ∈ P, (1 + c p)) - 1) := by
      rw [← Finset.mul_sum, ← hexpand]

theorem finite_fiber_product_bound {α ι : Type*} [Fintype α] [Fintype ι]
    (γ : ι → Type*) [∀ i, Fintype (γ i)]
    (mass : α → ℝ) (v : α → ∀ i, γ i)
    (w f : ∀ i, γ i → ℝ) (C : ℝ)
    (hf : ∀ i a, 0 ≤ f i a)
    (hjoint : ∀ a : ∀ i, γ i,
      (∑ x, mass x * (if v x = a then 1 else 0)) ≤ C * ∏ i, w i (a i)) :
    (∑ x, mass x * ∏ i, f i (v x i)) ≤
      C * ∏ i, ∑ a : γ i, w i a * f i a := by
  classical
  have hsplit (x : α) :
      mass x * ∏ i, f i (v x i) =
        ∑ a : ∀ i, γ i,
          (mass x * (if v x = a then 1 else 0)) * ∏ i, f i (a i) := by
    simp
  calc
    _ = ∑ a : ∀ i, γ i,
        (∑ x, mass x * (if v x = a then 1 else 0)) * ∏ i, f i (a i) := by
      simp_rw [hsplit]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
    _ ≤ ∑ a : ∀ i, γ i, (C * ∏ i, w i (a i)) * ∏ i, f i (a i) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hjoint a)
        (Finset.prod_nonneg fun i hi => hf i (a i))
    _ = C * ∏ i, ∑ a : γ i, w i a * f i a := by
      simp_rw [mul_assoc, ← Finset.prod_mul_distrib]
      rw [← Finset.mul_sum]
      congr 1
      simpa using (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (γ i)))
        (fun i a => w i a * f i a)).symm

end LinearFormsAux

set_option maxHeartbeats 2000000 in
private theorem linearForms_jointLocalBeta_moment {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (N : ℕ)
    (hlog : ∀ i : Fin n,
      4 * (primorial (N + 1) : ℝ) ≤
        Real.log (S.core.parameters.X N i : ℝ))
    (T : Finset ℕ) (hT : T ⊆ linearFormsPrimeSet D N)
    (H C₁ : ℝ) (hH : 0 ≤ H) (hC₁ : 0 ≤ C₁)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ L : ℕ,
      (∑ a ∈ Fintype.piFinset (fun _ : Fin q => Finset.range (L + 1)),
        comparisonPrimeValuationWeight (b := b) p a * averagedLocalBeta H p a) ≤
          C₁ / (p : ℝ) ^ 2) :
    (∑ σ ∈ linearFormsDivisorTupleSupport D N,
      linearFormsDivisorTupleMass D N σ *
        ∏ p ∈ T, averagedLocalBeta H p (linearFormsValVector σ p)) ≤
      (6 : ℝ) ^ (b * q) * ∏ p ∈ T, C₁ / (p : ℝ) ^ 2 := by
  classical
  let support := linearFormsDivisorTupleSupport D N
  let W : ℕ := primorial (N + 1)
  let PrimeIndex := {p : ℕ // p ∈ T}
  let Box : Finset (Fin q → ℕ) :=
    Fintype.piFinset (fun _ : Fin q => Finset.range (D.V N + 1))
  let Gamma := {a : Fin q → ℕ // a ∈ Box}
  let Alpha := {σ : Fin q → ℕ // σ ∈ support}
  letI : Fintype PrimeIndex := Finset.fintypeCoeSort T
  letI : Fintype Gamma := Finset.fintypeCoeSort Box
  letI : DecidableEq Gamma := Classical.decEq Gamma
  letI : Fintype Alpha := Finset.fintypeCoeSort support
  let mass : Alpha → ℝ := fun x => linearFormsDivisorTupleMass D N x.val
  let v : Alpha → (∀ p : PrimeIndex, Gamma) := fun x p =>
    ⟨linearFormsValVector x.val p.val, Fintype.mem_piFinset.mpr (by
      intro u
      apply Finset.mem_range.mpr
      have hσ := (linearFormsDivisorTuple_support_facts D N).2.2.2 x.val x.property u
      have hexp := Nat.factorization_lt p.val (Nat.ne_of_gt hσ.1)
      have hbound : Nat.factorization (x.val u) p.val ≤ D.V N := by omega
      exact Nat.lt_succ_of_le hbound)⟩
  let weight : ∀ p : PrimeIndex, Gamma → ℝ := fun p a =>
    comparisonPrimeValuationWeight (b := b) p.val a.val
  let factor : ∀ p : PrimeIndex, Gamma → ℝ := fun p a =>
    averagedLocalBeta H p.val a.val
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp (hT hp)).2
  have hcop : ∀ p ∈ T, Nat.Coprime p W := by
    intro p hp
    have hpIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp (hT hp)).1
    have hpp := hprime p hp
    apply hpp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hpSmall : p ≤ N + 1 := by
      apply hpp.dvd_primorial_iff.mp
      simpa [W] using hdiv
    omega
  have hscaleX (i : Fin n) : 4 * W ≤ S.core.parameters.X N i :=
    S.gapStage.valid_raw_cutoffs N i
  have hlogW (i : Fin n) :
      4 * (W : ℝ) ≤ Real.log (S.core.parameters.X N i : ℝ) := by
    simpa [W] using hlog i
  have hfactorNonneg (p : PrimeIndex) (a : Gamma) : 0 ≤ factor p a := by
    have hp := hprime p.val p.property
    have hreg := regularPrimeLocalExcess_nonneg p.val hp a.val
    have hex := exceptionalPrimeLocalExcess_nonneg p.val hp a.val
    dsimp [factor, averagedLocalBeta]
    exact add_nonneg hreg (mul_nonneg (div_nonneg hH (Nat.cast_nonneg _)) hex)
  have hweightNonneg (p : PrimeIndex) (a : Gamma) : 0 ≤ weight p a := by
    dsimp [weight, comparisonPrimeValuationWeight]
    apply Finset.prod_nonneg
    intro u hu
    positivity
  have hlocalGamma (p : PrimeIndex) :
      (∑ a : Gamma, weight p a * factor p a) ≤ C₁ / (p.val : ℝ) ^ 2 := by
    have hp := hprime p.val p.property
    have hlocal' := hlocal p.val hp (D.V N)
    have heq :
      (∑ a : Gamma, weight p a * factor p a) =
          ∑ a ∈ Box, comparisonPrimeValuationWeight (b := b) p.val a *
            averagedLocalBeta H p.val a := by
      simpa [weight, factor, Gamma, Box, comparisonPrimeValuationWeight] using
        (Finset.sum_subtype (F := (inferInstance : Fintype Gamma)) Box (fun a => Iff.rfl)
          (fun a => comparisonPrimeValuationWeight (b := b) p.val a *
            averagedLocalBeta H p.val a)).symm
    rw [heq]
    exact hlocal'
  let aNat (a : ∀ p : PrimeIndex, Gamma) : ℕ → Fin q → ℕ := fun p u =>
    if hp : p ∈ T then (a ⟨p, hp⟩).val u else 0
  have hvEq (x : Alpha) (a : ∀ p : PrimeIndex, Gamma) :
      (v x = a) ↔ ∀ u, ∀ p ∈ T,
        Nat.factorization (x.val u) p = aNat a p u := by
    constructor
    · intro heq u p hp
      let p' : PrimeIndex := ⟨p, hp⟩
      have h := congrArg (fun z : Gamma => z.val u) (congrFun heq p')
      have hval : Nat.factorization (x.val u) p = (a p').val u := by
        simpa [v, linearFormsValVector] using h
      have hindex : aNat a p u = (a p').val u := by
        simp [aNat, hp, p']
      rw [hindex]
      exact hval
    · intro heq
      funext p
      apply Subtype.ext
      funext u
      simpa [v, aNat, linearFormsValVector] using heq u p.val p.property
  have hfiberEq (a : ∀ p : PrimeIndex, Gamma) :
      (∑ x : Alpha, mass x * (if v x = a then 1 else 0)) =
        ∑ σ ∈ support, linearFormsDivisorTupleMass D N σ *
          (if ∀ u, ∀ p ∈ T, Nat.factorization (σ u) p = aNat a p u then 1 else 0) := by
    let g : (Fin q → ℕ) → ℝ := fun σ =>
      linearFormsDivisorTupleMass D N σ *
        (if ∀ u, ∀ p ∈ T, Nat.factorization (σ u) p = aNat a p u then 1 else 0)
    calc
      (∑ x : Alpha, mass x * (if v x = a then 1 else 0)) =
          ∑ x : Alpha, g x.val := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [g, mass]
            rw [if_congr (hvEq x a)]
            all_goals rfl
      _ = ∑ σ ∈ support, g σ := by
            change (∑ x ∈ support.attach, g x) = ∑ σ ∈ support, g σ
            exact (Finset.sum_subtype support (fun σ => Iff.rfl) g).symm
      _ = _ := by rfl
  have hzeroFiber (a : ∀ p : PrimeIndex, Gamma) (σ : Fin q → ℕ)
      (hσ : σ ∉ support) :
      linearFormsDivisorTupleMass D N σ *
        (if ∀ u, ∀ p ∈ T, Nat.factorization (σ u) p = aNat a p u then 1 else 0) = 0 := by
    rw [(linearFormsDivisorTuple_support_facts D N).2.2.1 σ hσ]
    simp
  have hsubProd (g : ℕ → ℝ) :
      (∏ p : PrimeIndex, g p.val) = ∏ p ∈ T, g p := by
    simpa [PrimeIndex] using
      (Finset.prod_subtype (p := fun p : ℕ => p ∈ T)
        (F := (inferInstance : Fintype PrimeIndex)) (s := T)
        (h := fun p : ℕ => Iff.rfl) (f := g)).symm
  have hfiberBound (a : ∀ p : PrimeIndex, Gamma) :
      (∑ x : Alpha, mass x * (if v x = a then 1 else 0)) ≤
        (6 : ℝ) ^ (b * q) * ∏ p : PrimeIndex, weight p (a p) := by
    let term (p : ℕ) (u : Fin q) : ℝ :=
      (((aNat a p u + 1 : ℕ) : ℝ) ^ b) / (p : ℝ) ^ (aNat a p u)
    have hmassBound := divisorTuplePrimeVectorMass_le D N W
      (by dsimp [W]; exact primorial_pos _) (by rfl) T hprime hcop hscaleX hlogW
      (aNat a)
    have hproduct :
        (∏ u : Fin q, (6 : ℝ) ^ b * ∏ p ∈ T, term p u) =
          (6 : ℝ) ^ (b * q) * ∏ p : PrimeIndex, weight p (a p) := by
      calc
        _ = (∏ u : Fin q, (6 : ℝ) ^ b) *
              ∏ u : Fin q, ∏ p ∈ T, term p u := by rw [Finset.prod_mul_distrib]
        _ = (6 : ℝ) ^ (b * q) * ∏ p ∈ T, ∏ u : Fin q, term p u := by
              rw [Finset.prod_comm]
              simp [Finset.prod_const, Fintype.card_fin, pow_mul]
        _ = (6 : ℝ) ^ (b * q) * ∏ p : PrimeIndex, weight p (a p) := by
              congr 1
              rw [← hsubProd (fun p => ∏ u : Fin q, term p u)]
              apply Finset.prod_congr rfl
              intro p hp
              change (∏ u : Fin q, term p u) =
                comparisonPrimeValuationWeight (b := b) p.val (a p).val
              simp [term, aNat, weight, comparisonPrimeValuationWeight, p.property]
    calc
      _ = ∑ σ ∈ support, linearFormsDivisorTupleMass D N σ *
          (if ∀ u, ∀ p ∈ T, Nat.factorization (σ u) p = aNat a p u then 1 else 0) :=
            hfiberEq a
      _ = ∑' σ : Fin q → ℕ, linearFormsDivisorTupleMass D N σ *
          (if ∀ u, ∀ p ∈ T, Nat.factorization (σ u) p = aNat a p u then 1 else 0) :=
            (tsum_eq_sum (s := support) (hzeroFiber a)).symm
      _ ≤ ∏ u : Fin q, (6 : ℝ) ^ b * ∏ p ∈ T, term p u := hmassBound
      _ = (6 : ℝ) ^ (b * q) * ∏ p : PrimeIndex, weight p (a p) := hproduct
  have hmoment := LinearFormsAux.finite_fiber_product_bound
      (fun _ : PrimeIndex => Gamma) mass v weight factor ((6 : ℝ) ^ (b * q))
      (by intro p a; exact hfactorNonneg p a) hfiberBound
  have hlocalSumNonneg (p : PrimeIndex) :
      0 ≤ ∑ a : Gamma, weight p a * factor p a := by
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hweightNonneg p a) (hfactorNonneg p a)
  have hprodBound :
      (∏ p : PrimeIndex, ∑ a : Gamma, weight p a * factor p a) ≤
        ∏ p : PrimeIndex, C₁ / (p.val : ℝ) ^ 2 := by
    apply finset_prod_le_prod_of_nonneg Finset.univ
    · intro p hp
      exact hlocalSumNonneg p
    · intro p hp
      positivity
    · intro p hp
      exact hlocalGamma p
  have hsumOuter :
      (∑ σ ∈ support, linearFormsDivisorTupleMass D N σ *
        ∏ p ∈ T, averagedLocalBeta H p (linearFormsValVector σ p)) =
      ∑ x : Alpha, mass x * ∏ p : PrimeIndex, factor p (v x p) := by
    calc
      _ = ∑ σ ∈ support, linearFormsDivisorTupleMass D N σ *
          ∏ p : PrimeIndex, averagedLocalBeta H p (linearFormsValVector σ p.val) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            congr 1
            exact (hsubProd (fun p => averagedLocalBeta H p
              (linearFormsValVector σ p))).symm
      _ = ∑ x : Alpha, mass x * ∏ p : PrimeIndex, factor p (v x p) := by
            exact (Finset.sum_subtype support (fun σ => Iff.rfl)
              (fun σ => linearFormsDivisorTupleMass D N σ *
                ∏ p : PrimeIndex, averagedLocalBeta H p.val
                  (linearFormsValVector σ p.val)))
  calc
    _ = ∑ x : Alpha, mass x * ∏ p : PrimeIndex, factor p (v x p) := hsumOuter
    _ ≤ (6 : ℝ) ^ (b * q) *
        ∏ p : PrimeIndex, ∑ a : Gamma, weight p a * factor p a := hmoment
    _ ≤ (6 : ℝ) ^ (b * q) * ∏ p : PrimeIndex, C₁ / (p.val : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hprodBound (by positivity)
    _ = (6 : ℝ) ^ (b * q) * ∏ p ∈ T, C₁ / (p : ℝ) ^ 2 := by
      congr 1
      exact hsubProd (fun p => C₁ / (p : ℝ) ^ 2)

set_option maxHeartbeats 2000000 in
private theorem uniformPrimeTupleCRTLaw_product {m w V : ℕ}
    (g : ∀ p : CRTPrimeRange w V, (Fin m → Fin p.val) → ℝ) :
    (∑ r : Fin m → CRTResidues w V,
      uniformPrimeTupleCRTLaw w V r *
        ∏ p : CRTPrimeRange w V, g p (fun i => r i p)) =
      ∏ p : CRTPrimeRange w V,
        ∑ x : Fin m → Fin p.val, uniformUnitTupleMass p.val m x * g p x := by
  classical
  let α : CRTPrimeRange w V → Type := fun p => Fin m → Fin p.val
  let μ : ∀ p, α p → ℝ := fun p => uniformUnitTupleMass p.val m
  let swap := crtSlotPrimeSwapEquiv (m := m) (w := w) (V := V)
  calc
    _ = ∑ s : ∀ p : CRTPrimeRange w V, α p,
        (∏ p, μ p (s p)) * ∏ p, g p (s p) := by
          apply Fintype.sum_equiv swap
          intro r
          rw [uniformPrimeTupleCRTLaw_factor (fun p i => r i p)]
          rfl
    _ = ∑ s : ∀ p : CRTPrimeRange w V, α p,
        ∏ p, (μ p (s p) * g p (s p)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [← Finset.prod_mul_distrib]
    _ = ∏ p : CRTPrimeRange w V,
        ∑ x : α p, μ p x * g p x := by
          let s : ∀ p : CRTPrimeRange w V, Finset (α p) := fun _ => Finset.univ
          simpa [s] using (Finset.prod_univ_sum s
            (fun p x => μ p x * g p x)).symm

private def linearFormsLocalBeta {q m w V : ℕ}
    (tests : Finset (IntegerPolynomial m))
    (r : Fin m → CRTResidues w V) (p : CRTPrimeRange w V)
    (a : Fin q → ℕ) : ℝ :=
  regularPrimeLocalExcess p.val a +
    (if ∃ Q ∈ tests,
      (p.val : ℤ) ∣ evalIntegerPolynomial Q (fun i => ((r i p).val : ℤ)) then 1 else 0) *
      exceptionalPrimeLocalExcess p.val a

private theorem uniformCRT_localBeta_average {q m w V : ℕ}
    (tests : Finset (IntegerPolynomial m))
    (htests : ∀ Q ∈ tests, Q ≠ 0)
    (B : ℕ) (hB : 0 < B)
    (hsize : ∀ Q ∈ tests,
      integerPolynomialContent Q < B ∧ Q.totalDegree ≤ B)
    (p : CRTPrimeRange w V) (a : Fin q → ℕ) :
    (∑ r : Fin m → CRTResidues w V,
      uniformPrimeTupleCRTLaw w V r * linearFormsLocalBeta tests r p a) ≤
      regularPrimeLocalExcess p.val a +
        (2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / p.val) *
          exceptionalPrimeLocalExcess p.val a := by
  classical
  have htotal : (∑ r : Fin m → CRTResidues w V,
      uniformPrimeTupleCRTLaw w V r) = 1 := by
    have hprod := uniformPrimeTupleCRTLaw_product (m := m) (w := w) (V := V)
      (fun _ _ => (1 : ℝ))
    calc
      _ = ∏ p : CRTPrimeRange w V,
          ∑ x : Fin m → Fin p.val, uniformUnitTupleMass p.val m x := by
            simpa using hprod
      _ = 1 := by
        apply Finset.prod_eq_one
        intro p hp
        exact uniformUnitTupleMass_total p.val m
          (Nat.Prime.pos ((Finset.mem_filter.mp p.property).2))
  have hbad := uniformCRTTestBad_probability_bound tests htests B hB hsize p
  have hreg : 0 ≤ regularPrimeLocalExcess p.val a :=
    regularPrimeLocalExcess_nonneg p.val
      ((Finset.mem_filter.mp p.property).2) a
  have hex : 0 ≤ exceptionalPrimeLocalExcess p.val a :=
    exceptionalPrimeLocalExcess_nonneg p.val
      ((Finset.mem_filter.mp p.property).2) a
  let bad : (Fin m → CRTResidues w V) → Prop := fun r =>
    ∃ Q ∈ tests,
      (p.val : ℤ) ∣ evalIntegerPolynomial Q (fun i => ((r i p).val : ℤ))
  have hdecomp :
      (∑ r : Fin m → CRTResidues w V,
        uniformPrimeTupleCRTLaw w V r * linearFormsLocalBeta tests r p a) =
        regularPrimeLocalExcess p.val a *
          ∑ r : Fin m → CRTResidues w V, uniformPrimeTupleCRTLaw w V r +
        exceptionalPrimeLocalExcess p.val a *
          ∑ r : Fin m → CRTResidues w V,
            uniformPrimeTupleCRTLaw w V r * (if bad r then 1 else 0) := by
    unfold linearFormsLocalBeta
    calc
      _ = ∑ r : Fin m → CRTResidues w V,
          (uniformPrimeTupleCRTLaw w V r * regularPrimeLocalExcess p.val a +
            (uniformPrimeTupleCRTLaw w V r * (if bad r then 1 else 0)) *
              exceptionalPrimeLocalExcess p.val a) := by
            apply Finset.sum_congr rfl
            intro r hr
            simp only [bad]
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
  have hbadEq :
      (∑ r : Fin m → CRTResidues w V,
        uniformPrimeTupleCRTLaw w V r * (if bad r then 1 else 0)) ≤
      2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / p.val := by
    simpa [bad] using hbad
  calc
    _ = regularPrimeLocalExcess p.val a +
        exceptionalPrimeLocalExcess p.val a *
          ∑ r : Fin m → CRTResidues w V,
            uniformPrimeTupleCRTLaw w V r * (if bad r then 1 else 0) := by
      rw [hdecomp, htotal]
      ring
    _ ≤ regularPrimeLocalExcess p.val a +
      exceptionalPrimeLocalExcess p.val a *
          (2 * (B : ℝ) * ((tests.card + 1 : ℕ) : ℝ) / p.val) :=
      by simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_left hbadEq hex)
          (regularPrimeLocalExcess p.val a))
    _ = _ := by ring


theorem prop_linear_forms {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    ∃ C : ℝ, 0 < C ∧ ∀ N (E : (Fin m → ℕ) → Prop),
      (∀ p, E p → D.goodDomain N p) →
      |weightedLinearFormsAverage D N E - weightedLinearFormsEventProbability D N E| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N)) := by
  sorry

/-- With master-scale CRT accuracy and base residue errors smaller than every fixed inverse
power of V, the linear-forms error tends to zero at each fixed row count. -/
theorem weighted_linear_forms_error_tends_zero {n q d b m : ℕ}
    {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : MasterScales n Aset m tests}
    (D : WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    Tendsto
      (fun N : ℕ => 1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
        (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
  have hVreal : Tendsto (fun N : ℕ => (D.V N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.V_tendsto
  have hinvV : Tendsto (fun N : ℕ => (D.V N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hVreal
  have hVpos : ∀ᶠ N : ℕ in atTop, 0 < (D.V N : ℝ) :=
    hVreal.eventually (eventually_gt_atTop 0)
  have hweighted (e : ℕ → ℝ) (he : SuperPolynomialSmall e (fun N => (D.V N : ℝ))) :
      Tendsto (fun N => (D.V N : ℝ) ^ q * e N) atTop (𝓝 0) := by
    have hs := he ((q : ℝ) + 1) (by positivity)
    have hpow (N : ℕ) : (D.V N : ℝ) ^ ((q : ℝ) + 1) =
        (D.V N : ℝ) ^ q * (D.V N : ℝ) := by
      have hexp : (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      simp [pow_succ]
    have hbase : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ))) atTop (𝓝 0) := by
      exact hs.congr fun N => by rw [hpow]
    have heq : (fun N =>
        e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) * (D.V N : ℝ)⁻¹) =ᶠ[atTop]
        (fun N => (D.V N : ℝ) ^ q * e N) := by
      filter_upwards [hVpos] with N hN
      field_simp [ne_of_gt hN]
    have hprod : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) * (D.V N : ℝ)⁻¹)
        atTop (𝓝 0) := by
      simpa using hbase.mul hinvV
    exact hprod.congr' heq
  have hbase := hweighted D.epsilonBase D.epsilonBase_superpolynomial
  have hcrt := hweighted D.epsilonCRT D.epsilonCRT_superpolynomial
  have hweightedSum : Tendsto
      (fun N => (D.V N : ℝ) ^ q * (D.epsilonBase N + D.epsilonCRT N))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun N => (D.V N : ℝ) ^ q * D.epsilonBase N +
          (D.V N : ℝ) ^ q * D.epsilonCRT N) atTop (𝓝 0) := by
      simpa using hbase.add hcrt
    apply hsum.congr'
    filter_upwards with N
    ring
  have hNplus : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro a
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop a)] with N hN
    exact le_trans hN (by norm_num)
  have hinvN : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNplus
  simpa [one_div] using hinvN.add hweightedSum


end
end HindmanSumsProducts
