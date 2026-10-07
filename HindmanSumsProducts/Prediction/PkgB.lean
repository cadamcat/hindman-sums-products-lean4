import HindmanSumsProducts.Prediction.Outside
import Mathlib.Analysis.MeanInequalities

/-! Helper lemmas for the §5 proof package S5-B (owned by its proof lane). -/

namespace HindmanSumsProducts

namespace Prediction

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
