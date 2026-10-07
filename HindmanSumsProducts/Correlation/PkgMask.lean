import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the §4 proof package `Mask` (owned by its proof lane). -/

namespace HindmanSumsProducts

open scoped BigOperators
open Filter
open FromArithmetic
attribute [local instance] Classical.propDecidable

theorem rationalResidue_eq_num_of_den_one {p : ℕ} (hp : p.Prime) (x : ℚ)
    (hx : x.den = 1) :
    FromArithmetic.rationalResidue p hp x = (x.num : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold FromArithmetic.rationalResidue
  rw [hx]
  simp only [Nat.cast_one, div_one]

theorem rationalResidue_intCast {p : ℕ} (hp : p.Prime) (z : ℤ) :
    FromArithmetic.rationalResidue p hp (z : ℚ) = (z : ZMod p) := by
  have h := rationalResidue_eq_num_of_den_one hp (z : ℚ) (by simp)
  simpa using h

theorem SuperPolynomialSmall.mul_rpow_tendsto {e V : ℕ → ℝ}
    (hsmall : SuperPolynomialSmall e V) (he : ∀ᶠ N in atTop, 0 ≤ e N)
    (hV : ∀ᶠ N in atTop, 1 ≤ V N) (B : ℝ) :
    Tendsto (fun N => e N * V N ^ B) atTop (nhds 0) := by
  let C := max B 1
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  have htop := hsmall C hC
  have hnonneg : ∀ᶠ N in atTop, 0 ≤ e N * V N ^ B := by
    filter_upwards [hV, he] with N hN heN
    exact mul_nonneg heN (Real.rpow_nonneg (by linarith) B)
  have hle : ∀ᶠ N in atTop, e N * V N ^ B ≤ e N * V N ^ C := by
    filter_upwards [hV, he] with N hN heN
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (le_max_left B 1)) heN
  exact squeeze_zero' hnonneg hle htop

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

def extendPrimeTuple {q : ℕ} (p : Fin q → ℕ) (p₀ : ℕ) : Fin (q + 1) → ℕ :=
  Fin.cases p₀ p

noncomputable def RowTemplate.scaleColumn {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    RowTemplate m (q + 1) := by
  classical
  let ext : Fin m → Option (Fin (q + 1) → ℕ) := fun k =>
    (T.entry k).map (fun e => Fin.cases (if k = u then 1 else 0) e)
  refine { entry := ext, support_nonempty := ?_, slots_disjoint := ?_ }
  · change (Finset.univ.filter fun k => (ext k).isSome).Nonempty
    have hsupport : Finset.univ.filter (fun k => (ext k).isSome) = T.support := by
      ext k
      cases T.entry k <;> simp [ext, RowTemplate.support]
    rw [hsupport]
    exact T.support_nonempty
  · intro k k' e e' hkk he he' i
    cases h₁ : T.entry k with
    | none => simp [ext, h₁] at he
    | some ek =>
      cases h₂ : T.entry k' with
      | none => simp [ext, h₂] at he'
      | some ek' =>
        simp [ext, h₁] at he
        simp [ext, h₂] at he'
        subst e
        subst e'
        refine Fin.cases ?_ (fun j => T.slots_disjoint k k' ek ek' hkk h₁ h₂ j) i
        by_cases hku : k = u
        · have hk'u : k' ≠ u := by
            intro hk'
            exact hkk (hku.trans hk'.symm)
          simp [hku, hk'u]
        · simp [hku]

noncomputable def RowTemplate.padSlot {m q : ℕ} (T : RowTemplate m q) :
    RowTemplate m (q + 1) := by
  classical
  let ext : Fin m → Option (Fin (q + 1) → ℕ) := fun k =>
    (T.entry k).map (fun e => Fin.cases 0 e)
  refine { entry := ext, support_nonempty := ?_, slots_disjoint := ?_ }
  · have hsupport : Finset.univ.filter (fun k => (ext k).isSome) = T.support := by
      ext k
      cases T.entry k <;> simp [ext, RowTemplate.support]
    rw [hsupport]
    exact T.support_nonempty
  · intro k k' e e' hkk he he' i
    cases h₁ : T.entry k with
    | none => simp [ext, h₁] at he
    | some ek =>
      cases h₂ : T.entry k' with
      | none => simp [ext, h₂] at he'
      | some ek' =>
        simp [ext, h₁] at he
        simp [ext, h₂] at he'
        subst e
        subst e'
        refine Fin.cases ?_ (fun j => T.slots_disjoint k k' ek ek' hkk h₁ h₂ j) i
        simp

theorem RowTemplate.padSlot_support {m q : ℕ} (T : RowTemplate m q) :
    T.padSlot.support = T.support := by
  classical
  ext k
  simp [RowTemplate.support, RowTemplate.padSlot]

theorem RowTemplate.padSlot_value {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (p₀ : ℕ) (k : Fin m) :
    T.padSlot.value (extendPrimeTuple p p₀) k = T.value p k := by
  classical
  cases h : T.entry k with
  | none => simp [RowTemplate.value, RowTemplate.padSlot, extendPrimeTuple, h]
  | some e =>
    simp [RowTemplate.value, RowTemplate.padSlot, extendPrimeTuple, h,
      Fin.prod_univ_succ]

def RowTemplate.ExponentsBinary {m q : ℕ} (T : RowTemplate m q) : Prop :=
  ∀ k e, T.entry k = some e → ∀ i, e i ≤ 1

theorem RowTemplate.scaleColumn_entry {m q : ℕ} (T : RowTemplate m q) (u k : Fin m)
    (e : Fin q → ℕ) (he : T.entry k = some e) :
    (T.scaleColumn u).entry k = some (Fin.cases (if k = u then 1 else 0) e) := by
  simp [RowTemplate.scaleColumn, he]

theorem RowTemplate.padSlot_entry {m q : ℕ} (T : RowTemplate m q) (k : Fin m)
    (e : Fin q → ℕ) (he : T.entry k = some e) :
    T.padSlot.entry k = some (Fin.cases 0 e) := by
  simp [RowTemplate.padSlot, he]

theorem RowTemplate.poly_entry {m q : ℕ} (T : RowTemplate m q) (k : Fin m)
    (e : Fin q → ℕ) (he : T.entry k = some e) :
    T.poly k = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
  simp [RowTemplate.poly, he]

theorem RowTemplate.scaleColumn_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) (u : Fin m) : (T.scaleColumn u).ExponentsBinary := by
  intro k e he i
  cases h : T.entry k with
  | none => simp [RowTemplate.scaleColumn, h] at he
  | some e₀ =>
    have hnew := T.scaleColumn_entry u k e₀ h
    have heq : Fin.cases (if k = u then 1 else 0) e₀ = e :=
      Option.some.inj (hnew.symm.trans he)
    subst e
    refine Fin.cases ?_ (fun j => hT k e₀ h j) i
    by_cases hku : k = u <;> simp [hku]

theorem RowTemplate.padSlot_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) : T.padSlot.ExponentsBinary := by
  intro k e he i
  cases h : T.entry k with
  | none => simp [RowTemplate.padSlot, h] at he
  | some e₀ =>
    have hnew := T.padSlot_entry k e₀ h
    have heq : Fin.cases 0 e₀ = e := Option.some.inj (hnew.symm.trans he)
    subst e
    refine Fin.cases ?_ (fun j => hT k e₀ h j) i
    norm_num

theorem rowForm_padSlot {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (p : Fin q → ℕ) (p₀ : ℕ) (z : Fin m → ℚ) :
    rowForm c T.padSlot (extendPrimeTuple p p₀) z = rowForm c T p z := by
  classical
  have hanchor : T.padSlot.anchor = T.anchor := by
    unfold RowTemplate.anchor
    apply (Finset.max'_eq_iff (s := T.padSlot.support)
      (H := T.padSlot.support_nonempty) T.anchor).2
    constructor
    · rw [T.padSlot_support]
      exact Finset.max'_mem T.support T.support_nonempty
    · intro b hb
      have hbT : b ∈ T.support := by rw [← T.padSlot_support]; exact hb
      exact Finset.le_max' T.support b hbT
  unfold rowForm
  rw [hanchor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.padSlot_value p p₀ k]

theorem RowTemplate.scaleColumn_support {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    (T.scaleColumn u).support = T.support := by
  classical
  ext k
  simp [RowTemplate.support, RowTemplate.scaleColumn]

theorem RowTemplate.scaleColumn_value {m q : ℕ} (T : RowTemplate m q) (u : Fin m)
    (p : Fin q → ℕ) (p₀ : ℕ) (k : Fin m) :
    (T.scaleColumn u).value (extendPrimeTuple p p₀) k =
      (if k = u then (p₀ : ℚ) else 1) * T.value p k := by
  classical
  cases h : T.entry k with
  | none => simp [RowTemplate.value, RowTemplate.scaleColumn, extendPrimeTuple, h]
  | some e =>
    simp [RowTemplate.value, RowTemplate.scaleColumn, extendPrimeTuple, h,
      Fin.prod_univ_succ]

theorem rowForm_scaleColumn {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (u : Fin m) (p : Fin q → ℕ) (p₀ : ℕ) (z : Fin m → ℚ) :
    rowForm c (T.scaleColumn u) (extendPrimeTuple p p₀) z =
      rowForm c T p (Function.update z u ((p₀ : ℚ) * z u)) := by
  classical
  have hanchor : (T.scaleColumn u).anchor = T.anchor := by
    unfold RowTemplate.anchor
    apply (Finset.max'_eq_iff (s := (T.scaleColumn u).support)
      (H := (T.scaleColumn u).support_nonempty) T.anchor).2
    constructor
    · rw [T.scaleColumn_support u]
      exact Finset.max'_mem T.support T.support_nonempty
    · intro b hb
      have hbT : b ∈ T.support := by
        rw [← T.scaleColumn_support u]
        exact hb
      exact Finset.le_max' T.support b hbT
  unfold rowForm
  rw [hanchor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.scaleColumn_value u p p₀ k]
  by_cases hku : k = u
  · subst k
    simp [Function.update_self]
    ring
  · have hupdate :
        Function.update z u ((p₀ : ℚ) * z u) k = z k := Function.update_of_ne hku _ _
    rw [hupdate]
    simp [hku]

noncomputable def RowTemplate.scaleBranchP {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    RowTemplate m (q + 2) := (T.scaleColumn u).padSlot

noncomputable def RowTemplate.scaleBranchQ {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    RowTemplate m (q + 2) := (T.padSlot).scaleColumn u

theorem rowForm_scaleBranchP {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (u : Fin m) (p : Fin q → ℕ) (p₁ p₀ : ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBranchP u) (extendPrimeTuple (extendPrimeTuple p p₁) p₀)
      (fun k => (z k : ℚ)) =
      rowForm c T p (Function.update (fun k => (z k : ℚ)) u
        ((p₁ : ℚ) * (z u : ℚ))) := by
  change rowForm c ((T.scaleColumn u).padSlot)
    (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) = _
  rw [rowForm_padSlot c (T.scaleColumn u) (extendPrimeTuple p p₁) p₀
    (fun k => (z k : ℚ))]
  exact rowForm_scaleColumn c T u p p₁ (fun k => (z k : ℚ))

theorem rowForm_scaleBranchQ {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (u : Fin m) (p : Fin q → ℕ) (p₁ p₀ : ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBranchQ u) (extendPrimeTuple (extendPrimeTuple p p₁) p₀)
      (fun k => (z k : ℚ)) =
      rowForm c T p (Function.update (fun k => (z k : ℚ)) u
        ((p₀ : ℚ) * (z u : ℚ))) := by
  change rowForm c ((T.padSlot).scaleColumn u)
    (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) = _
  rw [rowForm_scaleColumn c T.padSlot u (extendPrimeTuple p p₁) p₀
    (fun k => (z k : ℚ))]
  exact rowForm_padSlot c T p p₁
    (Function.update (fun k => (z k : ℚ)) u ((p₀ : ℚ) * (z u : ℚ)))

noncomputable def RowTemplate.scaleBalancedP {m q : ℕ} (T : RowTemplate m q) (u v : Fin m) :
    RowTemplate m (q + 2) := (T.scaleColumn v).scaleColumn u

noncomputable def RowTemplate.scaleBalancedQ {m q : ℕ} (T : RowTemplate m q) (u v : Fin m) :
    RowTemplate m (q + 2) := (T.scaleColumn u).scaleColumn v

theorem RowTemplate.scaleBranchP_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) (u : Fin m) : (T.scaleBranchP u).ExponentsBinary := by
  exact (T.scaleColumn u).padSlot_exponentsBinary (T.scaleColumn_exponentsBinary hT u)

theorem RowTemplate.scaleBranchQ_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) (u : Fin m) : (T.scaleBranchQ u).ExponentsBinary := by
  exact (T.padSlot).scaleColumn_exponentsBinary (T.padSlot_exponentsBinary hT) u

theorem RowTemplate.scaleBalancedP_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) (u v : Fin m) : (T.scaleBalancedP u v).ExponentsBinary := by
  exact (T.scaleColumn v).scaleColumn_exponentsBinary
    (T.scaleColumn_exponentsBinary hT v) u

theorem RowTemplate.scaleBalancedQ_exponentsBinary {m q : ℕ} (T : RowTemplate m q)
    (hT : T.ExponentsBinary) (u v : Fin m) : (T.scaleBalancedQ u v).ExponentsBinary := by
  exact (T.scaleColumn u).scaleColumn_exponentsBinary
    (T.scaleColumn_exponentsBinary hT u) v

theorem rowForm_scaleBalancedP {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (u v : Fin m) (huv : u ≠ v) (p : Fin q → ℕ) (p₁ p₀ : ℕ)
    (z : Fin m → ℤ) :
    rowForm c (T.scaleBalancedP u v)
      (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) =
      rowForm c T p
        (Function.update (Function.update (fun k => (z k : ℚ)) u
          ((p₀ : ℚ) * (z u : ℚ))) v ((p₁ : ℚ) * (z v : ℚ))) := by
  change rowForm c ((T.scaleColumn v).scaleColumn u)
    (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) = _
  rw [rowForm_scaleColumn c (T.scaleColumn v) u (extendPrimeTuple p p₁) p₀
    (fun k => (z k : ℚ))]
  rw [rowForm_scaleColumn c T v p p₁
    (Function.update (fun k => (z k : ℚ)) u ((p₀ : ℚ) * (z u : ℚ)))]
  have hv : Function.update (fun k => (z k : ℚ)) u ((p₀ : ℚ) * (z u : ℚ)) v =
      (z v : ℚ) := Function.update_of_ne (Ne.symm huv) _ _
  rw [hv]

theorem rowForm_scaleBalancedQ {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (u v : Fin m) (huv : u ≠ v) (p : Fin q → ℕ) (p₁ p₀ : ℕ)
    (z : Fin m → ℤ) :
    rowForm c (T.scaleBalancedQ u v)
      (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) =
      rowForm c T p
        (Function.update (Function.update (fun k => (z k : ℚ)) v
          ((p₀ : ℚ) * (z v : ℚ))) u ((p₁ : ℚ) * (z u : ℚ))) := by
  change rowForm c ((T.scaleColumn u).scaleColumn v)
    (extendPrimeTuple (extendPrimeTuple p p₁) p₀) (fun k => (z k : ℚ)) = _
  rw [rowForm_scaleColumn c (T.scaleColumn u) v (extendPrimeTuple p p₁) p₀
    (fun k => (z k : ℚ))]
  rw [rowForm_scaleColumn c T u p p₁
    (Function.update (fun k => (z k : ℚ)) v ((p₀ : ℚ) * (z v : ℚ)))]
  have hu : Function.update (fun k => (z k : ℚ)) v ((p₀ : ℚ) * (z v : ℚ)) u =
      (z u : ℚ) := Function.update_of_ne huv _ _
  rw [hu]

/-- Rational row coefficients viewed through the master prime-slot embedding. -/
def rowShapeLinearCoefficients {m q r s : ℕ} (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (c : Fin m → ℚ) :
    ℕ → (Fin s → ℕ) → Fin r → Fin m → ℚ :=
  fun _ p R k => c k / c (Sh.row R).anchor *
    (Sh.row R).value (fun i => p (ι i)) k

theorem linearRowValue_rowShape {m q r s : ℕ} (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (c : Fin m → ℚ) (N : ℕ) (p : Fin s → ℕ)
    (R : Fin r) (z : Fin m → ℤ) :
    FromArithmetic.linearRowValue (rowShapeLinearCoefficients Sh ι c) N p R z =
      rowForm c (Sh.row R) (fun i => p (ι i)) (fun k => (z k : ℚ)) := by
  rfl

theorem RowTemplate.entry_exists_of_mem_support {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (hk : k ∈ T.support) : ∃ e, T.entry k = some e := by
  have hsome : (T.entry k).isSome := (Finset.mem_filter.mp hk).2
  cases h : T.entry k with
  | none => simp [h] at hsome
  | some e => exact ⟨e, rfl⟩

theorem RowTemplate.poly_ne_zero_of_mem_support {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (hk : k ∈ T.support) : T.poly k ≠ 0 := by
  obtain ⟨e, he⟩ := T.entry_exists_of_mem_support k hk
  rw [T.poly_entry k e he]
  intro hz
  exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp hz)

theorem RowTemplate.parallel_of_all_minors_zero {m q : ℕ} {T T' : RowTemplate m q}
    (hminor : ∀ j k, T.poly j * T'.poly k - T.poly k * T'.poly j = 0) :
    T.Parallel T' := by
  classical
  have entry_exists {U : RowTemplate m q} (k : Fin m) (hk : k ∈ U.support) :
      ∃ e, U.entry k = some e := U.entry_exists_of_mem_support k hk
  have hsupport : T.support = T'.support := by
    apply Finset.Subset.antisymm
    · intro k hk
      by_contra hk'
      have hnone : T'.entry k = none := by
        cases h : T'.entry k with
        | none => rfl
        | some e => simp [RowTemplate.support, h] at hk'
      obtain ⟨j, hj⟩ := T'.support_nonempty
      have hleft : T.poly k * T'.poly j ≠ 0 :=
        mul_ne_zero (T.poly_ne_zero_of_mem_support k hk)
          (T'.poly_ne_zero_of_mem_support j hj)
      have hright : T.poly j * T'.poly k = 0 := by
        simp [RowTemplate.poly, hnone]
      have hz := hminor k j
      rw [hright, sub_zero] at hz
      exact hleft hz
    · intro k hk
      by_contra hk'
      have hnone : T.entry k = none := by
        cases h : T.entry k with
        | none => rfl
        | some e => simp [RowTemplate.support, h] at hk'
      obtain ⟨j, hj⟩ := T.support_nonempty
      have hleft : T.poly k * T'.poly j = 0 := by
        simp [RowTemplate.poly, hnone]
      have hright : T.poly j * T'.poly k ≠ 0 :=
        mul_ne_zero (T.poly_ne_zero_of_mem_support j hj)
          (T'.poly_ne_zero_of_mem_support k hk)
      have hz := hminor k j
      rw [hleft, zero_sub] at hz
      exact hright (neg_eq_zero.mp hz)
  obtain ⟨k₀, hk₀⟩ := T.support_nonempty
  obtain ⟨e₀, he₀⟩ := entry_exists k₀ hk₀
  have hk₀' : k₀ ∈ T'.support := by rw [← hsupport]; exact hk₀
  obtain ⟨e₀', he₀'⟩ := entry_exists k₀ hk₀'
  refine ⟨hsupport, ⟨fun i => (e₀' i : ℤ) - (e₀ i : ℤ), ?_⟩⟩
  intro k e e' he he' i
  have hk : k ∈ T.support := by simp [RowTemplate.support, he]
  have hk' : k ∈ T'.support := by rw [← hsupport]; exact hk
  have heqpoly : T.poly k * T'.poly k₀ = T.poly k₀ * T'.poly k :=
    sub_eq_zero.mp (hminor k k₀)
  rw [T.poly_entry k e he, T'.poly_entry k₀ e₀' he₀',
    T.poly_entry k₀ e₀ he₀, T'.poly_entry k e' he'] at heqpoly
  simp only [MvPolynomial.monomial_mul_monomial, one_mul] at heqpoly
  have hexp := MvPolynomial.monomial_left_injective
    (one_ne_zero : (1 : ℤ) ≠ 0) heqpoly
  have hnat : e i + e₀' i = e₀ i + e' i := by
    have hcoord := congrArg (fun f : Fin q →₀ ℕ => f i) hexp
    simpa using hcoord
  have hnatZ : (e i : ℤ) + (e₀' i : ℤ) = (e₀ i : ℤ) + (e' i : ℤ) := by
    exact_mod_cast hnat
  change (e' i : ℤ) = (e i : ℤ) + ((e₀' i : ℤ) - (e₀ i : ℤ))
  omega

theorem RowTemplate.exists_nonzero_minor_of_not_parallel {m q : ℕ}
    {T T' : RowTemplate m q} (h : ¬ T.Parallel T') :
    ∃ j k, T.poly j * T'.poly k - T.poly k * T'.poly j ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  exact h (T.parallel_of_all_minors_zero hnone)

theorem RowShape.nonparallel_minor_mem_templateMinors {m q r : ℕ}
    (Sh : RowShape m q r) (R I : Fin r) (hRI : R ≠ I) :
    ∃ P ∈ templateMinors Sh, ∃ j k,
      P = (Sh.row R).poly j * (Sh.row I).poly k -
        (Sh.row R).poly k * (Sh.row I).poly j := by
  obtain ⟨j, k, hne⟩ :=
    RowTemplate.exists_nonzero_minor_of_not_parallel (Sh.nonparallel R I hRI)
  let P := (Sh.row R).poly j * (Sh.row I).poly k -
    (Sh.row R).poly k * (Sh.row I).poly j
  have hmem : P ∈ templateMinors Sh := by
    unfold templateMinors
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      let x : Fin r × Fin r × Fin m × Fin m := (R, I, j, k)
      refine ⟨x, Finset.mem_univ x, ?_⟩
      rfl
    · exact hne
  exact ⟨P, hmem, j, k, rfl⟩

theorem RowTemplate.scaleBranchP_entry {m q : ℕ} (T : RowTemplate m q) (u k : Fin m)
    (e : Fin q → ℕ) (he : T.entry k = some e) :
    (T.scaleBranchP u).entry k =
      some (fun i => Fin.cases 0 (Fin.cases (if k = u then 1 else 0) e) i) := by
  simp [RowTemplate.scaleBranchP, RowTemplate.padSlot, RowTemplate.scaleColumn, he]

theorem RowTemplate.scaleBranchQ_entry {m q : ℕ} (T : RowTemplate m q) (u k : Fin m)
    (e : Fin q → ℕ) (he : T.entry k = some e) :
    (T.scaleBranchQ u).entry k =
      some (fun i => Fin.cases (if k = u then 1 else 0) (Fin.cases 0 e) i) := by
  simp [RowTemplate.scaleBranchQ, RowTemplate.padSlot, RowTemplate.scaleColumn, he]

theorem RowTemplate.scaleBranches_parallel_support {m q : ℕ}
    (T : RowTemplate m q) (u : Fin m)
    (hpar : (T.scaleBranchP u).Parallel (T.scaleBranchQ u)) :
    u ∉ T.support ∨ T.support = {u} := by
  rcases hpar with ⟨_, ⟨δ, hδ⟩⟩
  have hindicator (k : Fin m) (hk : k ∈ T.support) :
      (if k = u then (1 : ℤ) else 0) = δ (0 : Fin (q + 2)) := by
    obtain ⟨e, he⟩ := T.entry_exists_of_mem_support k hk
    have heP := T.scaleBranchP_entry u k e he
    have heQ := T.scaleBranchQ_entry u k e he
    let eP : Fin (q + 2) → ℕ :=
      @Fin.cases (q + 1) (fun _ : Fin (q + 2) => ℕ) 0
        (fun i => @Fin.cases q (fun _ : Fin (q + 1) => ℕ)
          (if k = u then 1 else 0) e i)
    let eQ : Fin (q + 2) → ℕ :=
      @Fin.cases (q + 1) (fun _ : Fin (q + 2) => ℕ)
        (if k = u then 1 else 0)
        (fun i => @Fin.cases q (fun _ : Fin (q + 1) => ℕ) 0 e i)
    have hrel := hδ k
      eP eQ heP heQ
      (0 : Fin (q + 2))
    have hQval : eQ (0 : Fin (q + 2)) = if k = u then 1 else 0 := rfl
    have hPval : eP (0 : Fin (q + 2)) = 0 := rfl
    rw [hQval, hPval, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hrel
    simpa using hrel
  by_cases hanchor : T.anchor = u
  · right
    ext k
    constructor
    · intro hk
      by_cases hku : k = u
      · exact Finset.mem_singleton.mpr hku
      · have hk0 : (0 : ℤ) = δ 0 := by
          simpa [hku] using hindicator k hk
        have hu1 : (1 : ℤ) = δ 0 := by
          simpa [hanchor] using
            hindicator T.anchor (Finset.max'_mem T.support T.support_nonempty)
        omega
    · intro hk
      have hku : k = u := Finset.mem_singleton.mp hk
      subst k
      rw [← hanchor]
      exact Finset.max'_mem T.support T.support_nonempty
  · left
    intro hu
    have hu' := hindicator u hu
    have ha' := hindicator T.anchor (Finset.max'_mem T.support T.support_nonempty)
    have hneq : T.anchor ≠ u := by simpa [eq_comm] using hanchor
    simp [hu, hneq] at hu' ha'
    omega

theorem RowTemplate.scaleBalancedP_entry {m q : ℕ} (T : RowTemplate m q)
    (u v k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) :
    (T.scaleBalancedP u v).entry k =
      some (fun i => Fin.cases (if k = u then 1 else 0)
        (Fin.cases (if k = v then 1 else 0) e) i) := by
  simp [RowTemplate.scaleBalancedP, RowTemplate.scaleColumn, he]

theorem RowTemplate.scaleBalancedQ_entry {m q : ℕ} (T : RowTemplate m q)
    (u v k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) :
    (T.scaleBalancedQ u v).entry k =
      some (fun i => Fin.cases (if k = v then 1 else 0)
        (Fin.cases (if k = u then 1 else 0) e) i) := by
  simp [RowTemplate.scaleBalancedQ, RowTemplate.scaleColumn, he]

theorem RowTemplate.scaleBalancedBranches_parallel_support {m q : ℕ}
    (T : RowTemplate m q) (u v : Fin m) (huv : u ≠ v)
    (hpar : (T.scaleBalancedP u v).Parallel (T.scaleBalancedQ u v)) :
    (u ∉ T.support ∧ v ∉ T.support) ∨ T.support = {u} ∨ T.support = {v} := by
  rcases hpar with ⟨_, ⟨δ, hδ⟩⟩
  have hdelta (k : Fin m) (hk : k ∈ T.support) :
      (if k = v then (1 : ℤ) else 0) =
        (if k = u then (1 : ℤ) else 0) + δ 0 := by
    obtain ⟨e, he⟩ := T.entry_exists_of_mem_support k hk
    have heP := T.scaleBalancedP_entry u v k e he
    have heQ := T.scaleBalancedQ_entry u v k e he
    let eP : Fin (q + 2) → ℕ :=
      @Fin.cases (q + 1) (fun _ : Fin (q + 2) => ℕ)
        (if k = u then 1 else 0)
        (fun i => @Fin.cases q (fun _ : Fin (q + 1) => ℕ)
          (if k = v then 1 else 0) e i)
    let eQ : Fin (q + 2) → ℕ :=
      @Fin.cases (q + 1) (fun _ : Fin (q + 2) => ℕ)
        (if k = v then 1 else 0)
        (fun i => @Fin.cases q (fun _ : Fin (q + 1) => ℕ)
          (if k = u then 1 else 0) e i)
    have hrel := hδ k
      eP eQ heP heQ (0 : Fin (q + 2))
    have hPval : eP (0 : Fin (q + 2)) = if k = u then 1 else 0 := rfl
    have hQval : eQ (0 : Fin (q + 2)) = if k = v then 1 else 0 := rfl
    rw [hPval, hQval, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hrel
    simpa using hrel
  by_cases hau : T.anchor = u
  · right
    left
    ext k
    constructor
    · intro hk
      by_cases hkv : k = v
      · have hk' := hdelta k hk
        have hu' := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
        simp [hau, huv, hkv] at hk' hu'
        omega
      · by_cases hku : k = u
        · exact Finset.mem_singleton.mpr hku
        · have hk' := hdelta k hk
          have hu' := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
          simp [hau, hkv, hku] at hk' hu'
          omega
    · intro hk
      have hku : k = u := Finset.mem_singleton.mp hk
      subst k
      rw [← hau]
      exact Finset.max'_mem T.support T.support_nonempty
  · by_cases hav : T.anchor = v
    · right
      right
      ext k
      constructor
      · intro hk
        by_cases hku : k = u
        · have hk' := hdelta k hk
          have hv' := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
          simp [hav, huv, hku] at hk' hv'
          omega
        · by_cases hkv : k = v
          · exact Finset.mem_singleton.mpr hkv
          · have hk' := hdelta k hk
            have hv' := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
            simp [hav, hku, hkv] at hk' hv'
            omega
      · intro hk
        have hkv : k = v := Finset.mem_singleton.mp hk
        subst k
        rw [← hav]
        exact Finset.max'_mem T.support T.support_nonempty
    · left
      constructor
      · intro hu
        have hU := hdelta u hu
        have hA := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
        simp [hau, hav, huv] at hU hA
        omega
      · intro hv
        have hV := hdelta v hv
        have hA := hdelta T.anchor (Finset.max'_mem T.support T.support_nonempty)
        simp [hau, hav, huv] at hV hA
        omega

theorem RowTemplate.scaleBranchP_support {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    (T.scaleBranchP u).support = T.support := by
  change (T.scaleColumn u).padSlot.support = T.support
  calc
    (T.scaleColumn u).padSlot.support = (T.scaleColumn u).support :=
      RowTemplate.padSlot_support (T.scaleColumn u)
    _ = T.support := T.scaleColumn_support u

theorem RowTemplate.scaleBranchQ_support {m q : ℕ} (T : RowTemplate m q) (u : Fin m) :
    (T.scaleBranchQ u).support = T.support := by
  change ((T.padSlot).scaleColumn u).support = T.support
  calc
    ((T.padSlot).scaleColumn u).support = T.padSlot.support :=
      RowTemplate.scaleColumn_support (T.padSlot) u
    _ = T.support := T.padSlot_support

theorem RowTemplate.scaleBalancedP_support {m q : ℕ} (T : RowTemplate m q)
    (u v : Fin m) : (T.scaleBalancedP u v).support = T.support := by
  change ((T.scaleColumn v).scaleColumn u).support = T.support
  calc
    ((T.scaleColumn v).scaleColumn u).support = (T.scaleColumn v).support :=
      RowTemplate.scaleColumn_support (T.scaleColumn v) u
    _ = T.support := T.scaleColumn_support v

theorem RowTemplate.scaleBalancedQ_support {m q : ℕ} (T : RowTemplate m q)
    (u v : Fin m) : (T.scaleBalancedQ u v).support = T.support := by
  change ((T.scaleColumn u).scaleColumn v).support = T.support
  calc
    ((T.scaleColumn u).scaleColumn v).support = (T.scaleColumn u).support :=
      RowTemplate.scaleColumn_support (T.scaleColumn u) v
    _ = T.support := T.scaleColumn_support u

theorem RowTemplate.parallel_of_scaleBranchP {m q : ℕ} (T T' : RowTemplate m q)
    (u : Fin m) (hpar : (T.scaleBranchP u).Parallel (T'.scaleBranchP u)) :
    T.Parallel T' := by
  refine ⟨?_, ?_⟩
  · calc
      T.support = (T.scaleBranchP u).support := (T.scaleBranchP_support u).symm
      _ = (T'.scaleBranchP u).support := hpar.1
      _ = T'.support := T'.scaleBranchP_support u
  · rcases hpar.2 with ⟨δ, hδ⟩
    refine ⟨fun i => δ i.succ.succ, ?_⟩
    intro k e e' he he' i
    have hEp := T.scaleBranchP_entry u k e he
    have hEp' := T'.scaleBranchP_entry u k e' he'
    have h := hδ k _ _ hEp hEp' i.succ.succ
    simpa using h

theorem RowTemplate.parallel_of_scaleBranchQ {m q : ℕ} (T T' : RowTemplate m q)
    (u : Fin m) (hpar : (T.scaleBranchQ u).Parallel (T'.scaleBranchQ u)) :
    T.Parallel T' := by
  refine ⟨?_, ?_⟩
  · calc
      T.support = (T.scaleBranchQ u).support := (T.scaleBranchQ_support u).symm
      _ = (T'.scaleBranchQ u).support := hpar.1
      _ = T'.support := T'.scaleBranchQ_support u
  · rcases hpar.2 with ⟨δ, hδ⟩
    refine ⟨fun i => δ i.succ.succ, ?_⟩
    intro k e e' he he' i
    have hEp := T.scaleBranchQ_entry u k e he
    have hEp' := T'.scaleBranchQ_entry u k e' he'
    have h := hδ k _ _ hEp hEp' i.succ.succ
    simpa using h

theorem RowTemplate.parallel_of_scaleBalancedP {m q : ℕ}
    (T T' : RowTemplate m q) (u v : Fin m)
    (hpar : (T.scaleBalancedP u v).Parallel (T'.scaleBalancedP u v)) : T.Parallel T' := by
  refine ⟨?_, ?_⟩
  · calc
      T.support = (T.scaleBalancedP u v).support := (T.scaleBalancedP_support u v).symm
      _ = (T'.scaleBalancedP u v).support := hpar.1
      _ = T'.support := T'.scaleBalancedP_support u v
  · rcases hpar.2 with ⟨δ, hδ⟩
    refine ⟨fun i => δ i.succ.succ, ?_⟩
    intro k e e' he he' i
    have hEp := T.scaleBalancedP_entry u v k e he
    have hEp' := T'.scaleBalancedP_entry u v k e' he'
    have h := hδ k _ _ hEp hEp' i.succ.succ
    simpa using h

theorem RowTemplate.parallel_of_scaleBalancedQ {m q : ℕ}
    (T T' : RowTemplate m q) (u v : Fin m)
    (hpar : (T.scaleBalancedQ u v).Parallel (T'.scaleBalancedQ u v)) : T.Parallel T' := by
  refine ⟨?_, ?_⟩
  · calc
      T.support = (T.scaleBalancedQ u v).support := (T.scaleBalancedQ_support u v).symm
      _ = (T'.scaleBalancedQ u v).support := hpar.1
      _ = T'.support := T'.scaleBalancedQ_support u v
  · rcases hpar.2 with ⟨δ, hδ⟩
    refine ⟨fun i => δ i.succ.succ, ?_⟩
    intro k e e' he he' i
    have hEp := T.scaleBalancedQ_entry u v k e he
    have hEp' := T'.scaleBalancedQ_entry u v k e' he'
    have h := hδ k _ _ hEp hEp' i.succ.succ
    simpa using h

theorem RowTemplate.scaleBranches_not_parallel {m q : ℕ} (T : RowTemplate m q)
    (u : Fin m) (hu : u ∈ T.support)
    (hother : ∃ k ∈ T.support, k ≠ u) :
    ¬ (T.scaleBranchP u).Parallel (T.scaleBranchQ u) := by
  intro hpar
  obtain ⟨k, hk, hku⟩ := hother
  obtain ⟨eu, heu⟩ := T.entry_exists_of_mem_support u hu
  obtain ⟨ek, hek⟩ := T.entry_exists_of_mem_support k hk
  rcases hpar.2 with ⟨δ, hδ⟩
  have hpu := T.scaleBranchP_entry u u eu heu
  have hqu := T.scaleBranchQ_entry u u eu heu
  have hpk := T.scaleBranchP_entry u k ek hek
  have hqk := T.scaleBranchQ_entry u k ek hek
  have hAtU : (1 : ℤ) = 0 + δ 0 := by
    simpa using hδ u _ _ hpu hqu 0
  have hAtK : (0 : ℤ) = 0 + δ 0 := by
    simpa [hku] using hδ k _ _ hpk hqk 0
  omega

theorem RowTemplate.scaleBalanced_not_parallel {m q : ℕ} (T : RowTemplate m q)
    (u v : Fin m) (huv : u ≠ v) (hu : u ∈ T.support) (hv : v ∈ T.support) :
    ¬ (T.scaleBalancedP u v).Parallel (T.scaleBalancedQ u v) := by
  intro hpar
  obtain ⟨eu, heu⟩ := T.entry_exists_of_mem_support u hu
  obtain ⟨ev, hev⟩ := T.entry_exists_of_mem_support v hv
  rcases hpar.2 with ⟨δ, hδ⟩
  have hpu := T.scaleBalancedP_entry u v u eu heu
  have hqu := T.scaleBalancedQ_entry u v u eu heu
  have hpv := T.scaleBalancedP_entry u v v ev hev
  have hqv := T.scaleBalancedQ_entry u v v ev hev
  have hAtU : (0 : ℤ) = 1 + δ 0 := by
    simpa [huv] using hδ u _ _ hpu hqu 0
  have hAtV : (1 : ℤ) = 0 + δ 0 := by
    simpa [Ne.symm huv] using hδ v _ _ hpv hqv 0
  omega

theorem RowTemplate.parallel_old_of_twoSlotExtensions {m q : ℕ}
    (T T' : RowTemplate m q) (L R : RowTemplate m (q + 2))
    (hLT : L.support = T.support) (hRT : R.support = T'.support)
    (hL : ∀ k e, T.entry k = some e →
      ∃ eL, L.entry k = some eL ∧ ∀ i, eL i.succ.succ = e i)
    (hR : ∀ k e, T'.entry k = some e →
      ∃ eR, R.entry k = some eR ∧ ∀ i, eR i.succ.succ = e i)
    (hpar : L.Parallel R) : T.Parallel T' := by
  refine ⟨?_, ?_⟩
  · calc
      T.support = L.support := hLT.symm
      _ = R.support := hpar.1
      _ = T'.support := hRT
  · rcases hpar.2 with ⟨δ, hδ⟩
    refine ⟨fun i => δ i.succ.succ, ?_⟩
    intro k e e' he he' i
    obtain ⟨eL, heL, heLs⟩ := hL k e he
    obtain ⟨eR, heR, heRs⟩ := hR k e' he'
    have h := hδ k eL eR heL heR i.succ.succ
    rw [heLs i, heRs i] at h
    exact h

theorem RowTemplate.parallel_old_of_scaleBranchP_Q {m q : ℕ}
    (T T' : RowTemplate m q) (u : Fin m)
    (hpar : (T.scaleBranchP u).Parallel (T'.scaleBranchQ u)) : T.Parallel T' := by
  apply RowTemplate.parallel_old_of_twoSlotExtensions T T'
    (T.scaleBranchP u) (T'.scaleBranchQ u)
    (T.scaleBranchP_support u) (T'.scaleBranchQ_support u) ?_ ?_ hpar
  · intro k e he
    refine ⟨fun i => Fin.cases 0 (Fin.cases (if k = u then 1 else 0) e) i,
      T.scaleBranchP_entry u k e he, ?_⟩
    intro i
    simp
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = u then 1 else 0) (Fin.cases 0 e) i,
      T'.scaleBranchQ_entry u k e he, ?_⟩
    intro i
    simp

theorem RowTemplate.parallel_old_of_scaleBranchQ_P {m q : ℕ}
    (T T' : RowTemplate m q) (u : Fin m)
    (hpar : (T.scaleBranchQ u).Parallel (T'.scaleBranchP u)) : T.Parallel T' := by
  apply RowTemplate.parallel_old_of_twoSlotExtensions T T'
    (T.scaleBranchQ u) (T'.scaleBranchP u)
    (T.scaleBranchQ_support u) (T'.scaleBranchP_support u) ?_ ?_ hpar
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = u then 1 else 0) (Fin.cases 0 e) i,
      T.scaleBranchQ_entry u k e he, ?_⟩
    intro i
    simp
  · intro k e he
    refine ⟨fun i => Fin.cases 0 (Fin.cases (if k = u then 1 else 0) e) i,
      T'.scaleBranchP_entry u k e he, ?_⟩
    intro i
    simp

theorem RowTemplate.parallel_old_of_scaleBalancedP_Q {m q : ℕ}
    (T T' : RowTemplate m q) (u v : Fin m)
    (hpar : (T.scaleBalancedP u v).Parallel (T'.scaleBalancedQ u v)) : T.Parallel T' := by
  apply RowTemplate.parallel_old_of_twoSlotExtensions T T'
    (T.scaleBalancedP u v) (T'.scaleBalancedQ u v)
    (T.scaleBalancedP_support u v) (T'.scaleBalancedQ_support u v) ?_ ?_ hpar
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = u then 1 else 0)
      (Fin.cases (if k = v then 1 else 0) e) i,
      T.scaleBalancedP_entry u v k e he, ?_⟩
    intro i
    simp
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = v then 1 else 0)
      (Fin.cases (if k = u then 1 else 0) e) i,
      T'.scaleBalancedQ_entry u v k e he, ?_⟩
    intro i
    simp

theorem RowTemplate.parallel_old_of_scaleBalancedQ_P {m q : ℕ}
    (T T' : RowTemplate m q) (u v : Fin m)
    (hpar : (T.scaleBalancedQ u v).Parallel (T'.scaleBalancedP u v)) : T.Parallel T' := by
  apply RowTemplate.parallel_old_of_twoSlotExtensions T T'
    (T.scaleBalancedQ u v) (T'.scaleBalancedP u v)
    (T.scaleBalancedQ_support u v) (T'.scaleBalancedP_support u v) ?_ ?_ hpar
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = v then 1 else 0)
      (Fin.cases (if k = u then 1 else 0) e) i,
      T.scaleBalancedQ_entry u v k e he, ?_⟩
    intro i
    simp
  · intro k e he
    refine ⟨fun i => Fin.cases (if k = u then 1 else 0)
      (Fin.cases (if k = v then 1 else 0) e) i,
      T'.scaleBalancedP_entry u v k e he, ?_⟩
    intro i
    simp

theorem RowTemplate.parallel_symm {m q : ℕ} {T T' : RowTemplate m q}
    (h : T.Parallel T') : T'.Parallel T := by
  rcases h with ⟨hs, ⟨δ, hδ⟩⟩
  refine ⟨hs.symm, ⟨fun i => -δ i, ?_⟩⟩
  intro k e e' he he' i
  have hcoeff := hδ k e' e he' he i
  linarith

def RowBranchIndex {r : ℕ} (I : Fin r → Prop) :=
  {x : Fin r × Fin 2 // x.2.val = 0 ∨ ¬ I x.1}

def pkgMask_RowBranchAllowed {r : ℕ} (I : Fin r → Prop) (i : Fin r) :=
  {b : Fin 2 // b.val = 0 ∨ ¬ I i}

noncomputable def pkgMask_rowBranchSigmaEquiv {r : ℕ} (I : Fin r → Prop) :
    RowBranchIndex I ≃ Σ i : Fin r, pkgMask_RowBranchAllowed I i := by
  refine
    { toFun := fun x => ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
      invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    cases x with
    | mk i b => cases b with | mk b hb => rfl

theorem pkgMask_prodRowBranchAllowed {r : ℕ} (I : Fin r → Prop)
    (i : Fin r) [Fintype (pkgMask_RowBranchAllowed I i)]
    (g : pkgMask_RowBranchAllowed I i → ℝ) :
    (∏ b : pkgMask_RowBranchAllowed I i, g b) =
      if hi : I i then g ⟨0, Or.inl rfl⟩ else
        g ⟨0, Or.inl rfl⟩ * g ⟨1, Or.inr hi⟩ := by
  classical
  letI : DecidablePred (fun b : Fin 2 => b.val = 0 ∨ ¬ I i) := Classical.decPred _
  by_cases hi : I i
  · let e : pkgMask_RowBranchAllowed I i ≃ PUnit.{1} :=
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => ⟨0, Or.inl rfl⟩
        left_inv := by
          intro b
          apply Subtype.ext
          apply Fin.ext
          rcases b.property with hb | hnot
          · exact hb.symm
          · exact False.elim (hnot hi)
        right_inv := by intro x; cases x; rfl }
    have hzero : e.symm PUnit.unit = ⟨0, Or.inl rfl⟩ := by
      apply Subtype.ext
      rfl
    calc
      (∏ b : pkgMask_RowBranchAllowed I i, g b) =
          ∏ x : PUnit.{1}, g (e.symm x) := (Equiv.prod_comp e.symm g).symm
      _ = g (e.symm PUnit.unit) := by simp
      _ = g ⟨0, Or.inl rfl⟩ := by rw [hzero]
      _ = if hi : I i then g ⟨0, Or.inl rfl⟩ else
            g ⟨0, Or.inl rfl⟩ * g ⟨1, Or.inr hi⟩ := by simp [hi]
  · let e : pkgMask_RowBranchAllowed I i ≃ Fin 2 :=
      { toFun := fun b => b.val
        invFun := fun b => ⟨b, Or.inr hi⟩
        left_inv := by intro b; apply Subtype.ext; rfl
        right_inv := by intro b; rfl }
    have hzero : e.symm (0 : Fin 2) = ⟨0, Or.inl rfl⟩ := by
      apply Subtype.ext
      rfl
    have hone : e.symm (1 : Fin 2) = ⟨1, Or.inr hi⟩ := by
      rfl
    calc
      (∏ b : pkgMask_RowBranchAllowed I i, g b) =
          ∏ b : Fin 2, g (e.symm b) := (Equiv.prod_comp e.symm g).symm
      _ = g ⟨0, Or.inl rfl⟩ * g ⟨1, Or.inr hi⟩ := by
        rw [Fin.prod_univ_two]
        rw [hzero, hone]
      _ = if hi : I i then g ⟨0, Or.inl rfl⟩ else
            g ⟨0, Or.inl rfl⟩ * g ⟨1, Or.inr hi⟩ := by simp [hi]

theorem pkgMask_rowBranchProduct_sigma {r : ℕ} (I : Fin r → Prop)
    [Fintype (RowBranchIndex I)]
    [∀ i : Fin r, Fintype (pkgMask_RowBranchAllowed I i)]
    (g : RowBranchIndex I → ℝ) :
    (∏ x : RowBranchIndex I, g x) =
      ∏ i : Fin r, ∏ b : pkgMask_RowBranchAllowed I i,
        g ⟨(i, b.val), b.property⟩ := by
  classical
  calc
    (∏ x : RowBranchIndex I, g x) =
        ∏ x : Σ i : Fin r, pkgMask_RowBranchAllowed I i,
          g ((pkgMask_rowBranchSigmaEquiv I).symm x) :=
      (Equiv.prod_comp (pkgMask_rowBranchSigmaEquiv I).symm g).symm
    _ = ∏ i : Fin r, ∏ b : pkgMask_RowBranchAllowed I i,
          g ((pkgMask_rowBranchSigmaEquiv I).symm ⟨i, b⟩) := by
      rw [Fintype.prod_sigma]

def RowBranchTemplate {m q r : ℕ} (Sh : RowShape m q r)
    (L R : Fin r → RowTemplate m (q + 2)) (i : Fin r) (b : Fin 2) :
    RowTemplate m (q + 2) :=
  if b.val = 0 then L i else R i

theorem exists_branch_row_shape {m q r : ℕ} (Sh : RowShape m q r)
    (L R : Fin r → RowTemplate m (q + 2)) (I : Fin r → Prop)
    (hI : ∀ i, I i ↔ (L i).Parallel (R i))
    (hAcross : ∀ i j, i ≠ j → ∀ b c : Fin 2,
      ¬ (RowBranchTemplate Sh L R i b).Parallel (RowBranchTemplate Sh L R j c))
    (hStar : ¬ I Sh.star) (Jstar : Finset (Fin m))
    (hStarSupport : (L Sh.star).support = Jstar) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r')
      (e : RowBranchIndex I ≃ Fin r'),
      (∀ x : RowBranchIndex I,
        Sh'.row (e x) = RowBranchTemplate Sh L R x.val.1 x.val.2) ∧
        r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧
          Sh'.star = e ⟨(Sh.star, 0), Or.inl rfl⟩ := by
  classical
  letI : DecidablePred I := Classical.decPred I
  let β := RowBranchIndex I
  letI : Finite β := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype β := Fintype.ofFinite β
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let btemp : Fin r × Fin 2 → RowTemplate m (q + 2) := fun x =>
    RowBranchTemplate Sh L R x.1 x.2
  have hnonparallel : ∀ i j, i ≠ j →
      ¬ (btemp ((e.symm i).val)).Parallel (btemp ((e.symm j).val)) := by
    intro i j hij
    let x := e.symm i
    let y := e.symm j
    have hxy : x ≠ y := by
      intro hEq
      apply hij
      have h := congrArg e hEq
      simpa [x, y] using h
    intro hpar
    by_cases hparent : x.val.1 = y.val.1
    · have hbits : x.val.2 ≠ y.val.2 := by
        intro hEq
        apply hxy
        exact Subtype.ext (Prod.ext hparent hEq)
      by_cases hx0 : x.val.2.val = 0
      · have hy1 : y.val.2.val = 1 := by omega
        have hnotI : ¬ I x.val.1 := by
          rcases y.property with hyzero | hnot
          · omega
          · simpa [hparent] using hnot
        have hparLR : (L x.val.1).Parallel (R x.val.1) := by
          have hpar' : (RowBranchTemplate Sh L R x.val.1 x.val.2).Parallel
              (RowBranchTemplate Sh L R y.val.1 y.val.2) := by
            simpa [btemp, x, y] using hpar
          simpa [RowBranchTemplate, hx0, hy1, hparent] using hpar'
        exact hnotI ((hI x.val.1).2 hparLR)
      · have hx1 : x.val.2.val = 1 := by omega
        have hy0 : y.val.2.val = 0 := by omega
        have hnotI : ¬ I x.val.1 := by
          rcases x.property with hxzero | hnot
          · omega
          · exact hnot
        have hparRL : (R x.val.1).Parallel (L x.val.1) := by
          have hpar' : (RowBranchTemplate Sh L R x.val.1 x.val.2).Parallel
              (RowBranchTemplate Sh L R y.val.1 y.val.2) := by
            simpa [btemp, x, y] using hpar
          simpa [RowBranchTemplate, hx1, hy0, hparent] using hpar'
        exact hnotI ((hI x.val.1).2 (RowTemplate.parallel_symm hparRL))
    · exact hAcross x.val.1 y.val.1 hparent x.val.2 y.val.2 (by
        simpa [btemp] using hpar)
  let Sh' : RowShape m (q + 2) (Fintype.card β) := {
    row := fun i => btemp ((e.symm i).val)
    star := e ⟨(Sh.star, 0), Or.inl rfl⟩
    nonparallel := hnonparallel
  }
  have hcard : Fintype.card β ≤ 2 * r := by
    calc
      Fintype.card β ≤ Fintype.card (Fin r × Fin 2) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = r * 2 := by simp
      _ = 2 * r := by omega
  have hstar : (Sh'.row Sh'.star).support = Jstar := by
    let xstar : β := ⟨(Sh.star, 0), Or.inl rfl⟩
    change (btemp (e.symm (e xstar)).val).support = Jstar
    rw [Equiv.symm_apply_apply]
    simp [btemp, RowBranchTemplate, xstar, hStarSupport]
  have hrowmap (x : β) : Sh'.row (e x) = btemp x.val := by
    change btemp (e.symm (e x)).val = btemp x.val
    simp
  refine ⟨Fintype.card β, Sh', e, ?_, hcard, hstar, rfl⟩
  intro x
  exact hrowmap x

theorem exists_scaleBranch_row_shape {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hStarSupport : (Sh.row Sh.star).support = Jstar)
    (u v : Fin m) (hu : u ∈ (Sh.row Sh.star).support)
    (hv : v ∈ (Sh.row Sh.star).support) (hvu : v ≠ u) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r')
      (e : RowBranchIndex (fun i =>
        ((Sh.row i).scaleBranchP u).Parallel ((Sh.row i).scaleBranchQ u)) ≃ Fin r'),
      (∀ x, Sh'.row (e x) = RowBranchTemplate Sh
        (fun i => (Sh.row i).scaleBranchP u)
        (fun i => (Sh.row i).scaleBranchQ u) x.val.1 x.val.2) ∧
        r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧
        Sh'.star = e ⟨(Sh.star, 0), Or.inl rfl⟩ := by
  let L : Fin r → RowTemplate m (q + 2) := fun i => (Sh.row i).scaleBranchP u
  let R : Fin r → RowTemplate m (q + 2) := fun i => (Sh.row i).scaleBranchQ u
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  have hI : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  have hAcross : ∀ i j, i ≠ j → ∀ b c : Fin 2,
      ¬ (RowBranchTemplate Sh L R i b).Parallel (RowBranchTemplate Sh L R j c) := by
    intro i j hij b c
    by_cases hb : b.val = 0
    · by_cases hc : c.val = 0
      · intro hpar
        have hp : ((Sh.row i).scaleBranchP u).Parallel ((Sh.row j).scaleBranchP u) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_of_scaleBranchP _ _ u hp)
      · intro hpar
        have hp : ((Sh.row i).scaleBranchP u).Parallel ((Sh.row j).scaleBranchQ u) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_old_of_scaleBranchP_Q _ _ u hp)
    · by_cases hc : c.val = 0
      · intro hpar
        have hp : ((Sh.row i).scaleBranchQ u).Parallel ((Sh.row j).scaleBranchP u) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_old_of_scaleBranchQ_P _ _ u hp)
      · intro hpar
        have hp : ((Sh.row i).scaleBranchQ u).Parallel ((Sh.row j).scaleBranchQ u) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_of_scaleBranchQ _ _ u hp)
  have hStar : ¬ I Sh.star := by
    change ¬ ((Sh.row Sh.star).scaleBranchP u).Parallel
      ((Sh.row Sh.star).scaleBranchQ u)
    apply RowTemplate.scaleBranches_not_parallel
    · exact hu
    · exact ⟨v, hv, hvu⟩
  have hTarget : (L Sh.star).support = Jstar := by
    dsimp [L]
    calc
      ((Sh.row Sh.star).scaleBranchP u).support = (Sh.row Sh.star).support :=
        RowTemplate.scaleBranchP_support _ _
      _ = Jstar := hStarSupport
  obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
    exists_branch_row_shape Sh L R I hI hAcross hStar Jstar hTarget
  refine ⟨r', Sh', ?_, ?_, hr', hstar', ?_⟩
  · simpa [I, L, R] using e
  · simpa [I, L, R, RowBranchTemplate] using hrow
  · simpa [I, L, R] using hstarIndex

theorem exists_scaleBalanced_row_shape {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hStarSupport : (Sh.row Sh.star).support = Jstar)
    (u v : Fin m) (hu : u ∈ (Sh.row Sh.star).support)
    (hv : v ∈ (Sh.row Sh.star).support) (huv : u ≠ v) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r')
      (e : RowBranchIndex (fun i =>
        ((Sh.row i).scaleBalancedP u v).Parallel ((Sh.row i).scaleBalancedQ u v)) ≃ Fin r'),
      (∀ x, Sh'.row (e x) = RowBranchTemplate Sh
        (fun i => (Sh.row i).scaleBalancedP u v)
        (fun i => (Sh.row i).scaleBalancedQ u v) x.val.1 x.val.2) ∧
        r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧
        Sh'.star = e ⟨(Sh.star, 0), Or.inl rfl⟩ := by
  let L : Fin r → RowTemplate m (q + 2) := fun i => (Sh.row i).scaleBalancedP u v
  let R : Fin r → RowTemplate m (q + 2) := fun i => (Sh.row i).scaleBalancedQ u v
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  have hI : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  have hAcross : ∀ i j, i ≠ j → ∀ b c : Fin 2,
      ¬ (RowBranchTemplate Sh L R i b).Parallel (RowBranchTemplate Sh L R j c) := by
    intro i j hij b c
    by_cases hb : b.val = 0
    · by_cases hc : c.val = 0
      · intro hpar
        have hp : ((Sh.row i).scaleBalancedP u v).Parallel
            ((Sh.row j).scaleBalancedP u v) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_of_scaleBalancedP _ _ u v hp)
      · intro hpar
        have hp : ((Sh.row i).scaleBalancedP u v).Parallel
            ((Sh.row j).scaleBalancedQ u v) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_old_of_scaleBalancedP_Q _ _ u v hp)
    · by_cases hc : c.val = 0
      · intro hpar
        have hp : ((Sh.row i).scaleBalancedQ u v).Parallel
            ((Sh.row j).scaleBalancedP u v) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_old_of_scaleBalancedQ_P _ _ u v hp)
      · intro hpar
        have hp : ((Sh.row i).scaleBalancedQ u v).Parallel
            ((Sh.row j).scaleBalancedQ u v) := by
          simpa [RowBranchTemplate, L, R, hb, hc] using hpar
        exact Sh.nonparallel i j hij (RowTemplate.parallel_of_scaleBalancedQ _ _ u v hp)
  have hStar : ¬ I Sh.star := by
    change ¬ ((Sh.row Sh.star).scaleBalancedP u v).Parallel
      ((Sh.row Sh.star).scaleBalancedQ u v)
    apply RowTemplate.scaleBalanced_not_parallel
    · exact huv
    · exact hu
    · exact hv
  have hTarget : (L Sh.star).support = Jstar := by
    dsimp [L]
    calc
      ((Sh.row Sh.star).scaleBalancedP u v).support = (Sh.row Sh.star).support :=
        RowTemplate.scaleBalancedP_support _ _ _
      _ = Jstar := hStarSupport
  obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
    exists_branch_row_shape Sh L R I hI hAcross hStar Jstar hTarget
  refine ⟨r', Sh', ?_, ?_, hr', hstar', ?_⟩
  · simpa [I, L, R] using e
  · simpa [I, L, R, RowBranchTemplate] using hrow
  · simpa [I, L, R] using hstarIndex

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

theorem mask_product_scale_at {m : ℕ} (U : Finset (Fin m)) (u : Fin m)
    (z : Fin m → ℤ) (p : ℤ) :
    (∏ k ∈ U, Function.update z u (p * z u) k) =
      (if u ∈ U then p else 1) * ∏ k ∈ U, z k := by
  by_cases hu : u ∈ U
  · have hrest : ∀ k ∈ U.erase u, Function.update z u (p * z u) k = z k := by
      intro k hk
      exact Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _
    calc
      (∏ k ∈ U, Function.update z u (p * z u) k) =
          Function.update z u (p * z u) u *
            ∏ k ∈ U.erase u, Function.update z u (p * z u) k :=
        (Finset.mul_prod_erase U _ hu).symm
      _ = (p * z u) * ∏ k ∈ U.erase u, z k := by
        simp only [Function.update_self]
        rw [Finset.prod_congr rfl hrest]
      _ = p * ∏ k ∈ U, z k := by
        rw [← Finset.mul_prod_erase U z hu]
        ring
      _ = (if u ∈ U then p else 1) * ∏ k ∈ U, z k := by simp [hu]
  · rw [mask_product_update_outside U u hu z (p * z u)]
    simp [hu]

theorem mask_product_scale_two {m : ℕ} (U : Finset (Fin m)) (u v : Fin m)
    (huv : u ≠ v) (z : Fin m → ℤ) (p q : ℤ) :
    (∏ k ∈ U,
      Function.update (Function.update z u (p * z u)) v
        (q * Function.update z u (p * z u) v) k) =
      (if u ∈ U then p else 1) * (if v ∈ U then q else 1) * ∏ k ∈ U, z k := by
  rw [mask_product_scale_at U v (Function.update z u (p * z u)) q]
  rw [mask_product_scale_at U u z p]
  ring

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

theorem harmonicNormalizer_pos_of_cutoff (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) : 0 < harmonicNormalizer X W := by
  classical
  have hXge4 : 4 ≤ X := by omega
  have hWleX : W ≤ X := by omega
  let n₀ : ℕ := (X / W + 1) * W + 1
  have hdiv : X / W * W + X % W = X := Nat.div_add_mod' X W
  have hmod : X % W < W := Nat.mod_lt X hW
  have hn₀eq : n₀ = X / W * W + W + 1 := by simp [n₀, Nat.add_mul]
  have hn₀lo : X < n₀ := by rw [hn₀eq]; omega
  have hquot : X / W * W ≤ X := Nat.div_mul_le_self X W
  have hn₀upper : n₀ ≤ 2 * X + 1 := by rw [hn₀eq]; omega
  have hXsqr : 2 * X + 1 < X ^ 2 := by
    have hXr : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
    have hmul : 0 ≤ (X : ℝ) * ((X : ℝ) - 3) :=
      mul_nonneg (by positivity) (by linarith)
    have h : (2 : ℝ) * X + 1 < (X : ℝ) ^ 2 := by nlinarith [hmul]
    exact_mod_cast h
  have hn₀hi : n₀ < X ^ 2 := lt_of_le_of_lt hn₀upper hXsqr
  have hn₀cop : Nat.Coprime n₀ W := by
    have h : Nat.Coprime (W * (X / W + 1) + 1) W :=
      (Nat.coprime_mul_left_add_left 1 W (X / W + 1)).2 (by simp)
    simpa [n₀, Nat.mul_comm] using h
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  have hn₀mem : n₀ ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hn₀lo.le, hn₀hi⟩, hn₀cop⟩
  have hn₀pos : 0 < n₀ := by omega
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀pos
  have hterm : (0 : ℝ) < 1 / (n₀ : ℝ) := one_div_pos.mpr hn₀R
  unfold harmonicNormalizer
  have hsum := Finset.single_le_sum (s := S) (f := fun n : ℕ => 1 / (n : ℝ))
    (fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n)) hn₀mem
  simpa [S] using lt_of_lt_of_le hterm hsum

theorem harmonicNatLaw_summable (X W : ℕ) : Summable (harmonicNatLaw X W) := by
  apply summable_of_ne_finset_zero (s := Finset.range (X ^ 2))
  intro n hn
  have hnlo : X ^ 2 ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  simp [harmonicNatLaw, hnlo]

theorem harmonicNatLaw_tsum_one_of_normalizer_pos (X W : ℕ)
    (hX : 0 < X) (hNorm : 0 < harmonicNormalizer X W) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  classical
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  have hzero (n : ℕ) (hn : n ∉ S) : harmonicNatLaw X W n = 0 := by
    by_contra hne
    have hcond : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W := by
      by_contra hnot
      have : harmonicNatLaw X W n = 0 := by simp [harmonicNatLaw, hnot]
      exact hne this
    apply hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hcond.1, hcond.2.1⟩, hcond.2.2⟩
  have hterm (n : ℕ) (hn : n ∈ S) :
      harmonicNatLaw X W n = (1 / (n : ℝ)) / harmonicNormalizer X W := by
    rcases Finset.mem_filter.mp hn with ⟨hnIco, hcop⟩
    rcases Finset.mem_Ico.mp hnIco with ⟨hXn, hnX2⟩
    have hnpos : 0 < n := lt_of_lt_of_le hX hXn
    have hnum : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnpos).ne'
    unfold harmonicNatLaw
    rw [if_pos ⟨hXn, hnX2, hcop⟩]
    field_simp
  calc
    (∑' n : ℕ, harmonicNatLaw X W n) = ∑ n ∈ S, harmonicNatLaw X W n :=
      tsum_eq_sum (s := S) hzero
    _ = ∑ n ∈ S, (1 / (n : ℝ)) / harmonicNormalizer X W := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n hn
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = 1 := by
      have hsum : (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W := by
        rfl
      rw [hsum]
      exact div_self hNorm.ne'

theorem harmonicNatLaw_sum_range_eq_one (X W : ℕ)
    (hX : 0 < X) (hNorm : 0 < harmonicNormalizer X W) :
    ∑ n ∈ Finset.range (X ^ 2), harmonicNatLaw X W n = 1 := by
  classical
  have hzero (n : ℕ) (hn : n ∉ Finset.range (X ^ 2)) :
      harmonicNatLaw X W n = 0 := by
    have hbound : X ^ 2 ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    simp [harmonicNatLaw, Nat.not_lt_of_ge hbound]
  calc
    ∑ n ∈ Finset.range (X ^ 2), harmonicNatLaw X W n =
        ∑' n : ℕ, harmonicNatLaw X W n :=
      (tsum_eq_sum (s := Finset.range (X ^ 2)) hzero).symm
    _ = 1 := harmonicNatLaw_tsum_one_of_normalizer_pos X W hX hNorm

theorem parameterTailProductLaw_eq_finite_sum {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) :
    FromArithmetic.parameterTailProductLaw A N T σ =
      ∑ t ∈ Fintype.piFinset
        (fun j : Fin n => Finset.range ((A.X N j) ^ 2)),
        (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
  classical
  let D : Finset (Fin n → ℕ) :=
    Fintype.piFinset fun j => Finset.range ((A.X N j) ^ 2)
  have hzero (t : Fin n → ℕ) (ht : t ∉ D) :
      (if (∏ j ∈ T, t j) = σ then 1 else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    have hnot : ¬ ∀ j, t j < (A.X N j) ^ 2 := by
      intro hall
      apply ht
      apply Fintype.mem_piFinset.mpr
      intro j
      simpa only [Finset.mem_range] using hall j
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    have hmass : harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
      have hlt : ¬ t j < (A.X N j) ^ 2 := by omega
      simp [harmonicNatLaw, hlt]
    have hprod : ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ)
        (f := fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))
        (Finset.mem_univ j) hmass
    simp [hprod]
  unfold FromArithmetic.parameterTailProductLaw
  exact tsum_eq_sum (s := D) hzero

theorem harmonicProductLaw_eq_finite_sum {q : ℕ}
    (W : ℕ) (X : Fin q → ℕ) (σ : ℕ) :
    harmonicProductLaw W X σ =
      ∑ t ∈ Fintype.piFinset (fun i : Fin q => Finset.range ((X i) ^ 2)),
        (if (∏ i, t i) = σ then 1 else 0) *
          ∏ i, harmonicNatLaw (X i) W (t i) := by
  classical
  let D : Finset (Fin q → ℕ) :=
    Fintype.piFinset fun i => Finset.range ((X i) ^ 2)
  have hzero (t : Fin q → ℕ) (ht : t ∉ D) :
      (if (∏ i, t i) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    have hnot : ¬ ∀ i, t i < (X i) ^ 2 := by
      intro hall
      apply ht
      apply Fintype.mem_piFinset.mpr
      intro i
      simpa only [Finset.mem_range] using hall i
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    have hmass : harmonicNatLaw (X i) W (t i) = 0 := by
      have hlt : ¬ t i < (X i) ^ 2 := by omega
      simp [harmonicNatLaw, hlt]
    have hprod : ∏ i, harmonicNatLaw (X i) W (t i) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ)
        (f := fun i => harmonicNatLaw (X i) W (t i))
        (Finset.mem_univ i) hmass
    simp [hprod]
  unfold harmonicProductLaw
  exact tsum_eq_sum (s := D) hzero

theorem harmonicProductLaw_coprime_of_ne_zero {q : ℕ} (W : ℕ)
    (X : Fin q → ℕ) (σ : ℕ)
    (hσ : harmonicProductLaw W X σ ≠ 0) : Nat.Coprime σ W := by
  classical
  by_contra hcop
  have hterm (t : Fin q → ℕ) :
      (if (∏ i, t i) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    by_cases hp : (∏ i, t i) = σ
    · have hnotAll : ¬ ∀ i, Nat.Coprime (t i) W := by
        intro hall
        have hprodCop : Nat.Coprime (∏ i, t i) W := by
          rw [Nat.coprime_fintype_prod_left_iff]
          exact hall
        exact hcop (by simpa [hp] using hprodCop)
      obtain ⟨i, hi⟩ := not_forall.mp hnotAll
      have hzero : harmonicNatLaw (X i) W (t i) = 0 := by
        simp [harmonicNatLaw, hi]
      have hprod : ∏ i, harmonicNatLaw (X i) W (t i) = 0 :=
        Finset.prod_eq_zero (s := Finset.univ)
          (f := fun i => harmonicNatLaw (X i) W (t i)) (Finset.mem_univ i) hzero
      simp [hp, hprod]
    · simp [hp]
  apply hσ
  rw [harmonicProductLaw_eq_finite_sum]
  apply Finset.sum_eq_zero
  intro t ht
  exact hterm t

theorem integerResidue_eq_natMod_of_nonneg {K : ℕ} (hK : 0 < K) {z : ℤ}
    (hz : 0 ≤ z) :
    FromArithmetic.integerResidue K hK z = ⟨z.toNat % K, Nat.mod_lt _ hK⟩ := by
  apply Fin.ext
  change (z % (K : ℤ)).toNat = z.toNat % K
  have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  have hmod : z % (K : ℤ) = ((z.toNat % K : ℕ) : ℤ) := by
    calc
      z % (K : ℤ) = (z.toNat : ℤ) % (K : ℤ) :=
        congrArg (fun x : ℤ => x % (K : ℤ)) hcast.symm
      _ = ((z.toNat % K : ℕ) : ℤ) := (Int.natCast_mod _ _).symm
  have hmodNonneg : 0 ≤ z % (K : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hK.ne')
  have hcastMod : ((z % (K : ℤ)).toNat : ℤ) = (z.toNat % K : ℤ) := by
    rw [Int.toNat_of_nonneg hmodNonneg, hmod]
    simp
  exact_mod_cast hcastMod

def finsetComplement {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) : Finset α :=
  Finset.univ.filter fun i => i ∉ T

def piFinsetSplit {n : ℕ} [DecidableEq (Fin n)] (T : Finset (Fin n)) :
    (Fin n → ℕ) ≃ ((∀ i : T, ℕ) × ∀ i : finsetComplement T, ℕ) := by
  letI : DecidablePred (fun j : Fin n => j ∈ T) :=
    fun j => Finset.decidableMem j T
  refine
    { toFun := fun f => (fun i => f i.1, fun i => f i.1)
      invFun := fun z j =>
        if hj : j ∈ T then z.1 ⟨j, hj⟩
        else z.2 ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    funext j
    by_cases hj : j ∈ T <;> simp [hj]
  · intro z
    rcases z with ⟨u, v⟩
    apply Prod.ext
    · funext i
      simp [i.property]
    · funext i
      have hi : (i : Fin n) ∉ T := by
        simpa [finsetComplement] using i.property
      simp [hi]

theorem piFinsetSplit_left_apply {n : ℕ} [DecidableEq (Fin n)]
    (T : Finset (Fin n)) (t : Fin n → ℕ) (i : T) :
    (piFinsetSplit T t).1 i = t i.val := by
  simp [piFinsetSplit, Equiv.piFinsetUnion, Equiv.piCongrLeft']

theorem piFinsetSplit_right_apply {n : ℕ} [DecidableEq (Fin n)]
    (T : Finset (Fin n)) (t : Fin n → ℕ) (i : finsetComplement T) :
    (piFinsetSplit T t).2 i = t i.val := by
  simp [piFinsetSplit, Equiv.piFinsetUnion, Equiv.piCongrLeft']

theorem parameterTailProductLaw_eq_split_sum {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) :
    FromArithmetic.parameterTailProductLaw A N T σ =
      ∑ z ∈
        Fintype.piFinset (fun i : T => Finset.range ((A.X N i.val) ^ 2)) ×ˢ
          Fintype.piFinset
            (fun i : finsetComplement T => Finset.range ((A.X N i.val) ^ 2)),
        (if (∏ i : T, z.1 i) = σ then 1 else 0) *
          ((∏ i : T,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.1 i)) *
            ∏ i : finsetComplement T,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.2 i)) := by
  classical
  let Tcomp := finsetComplement T
  let Dfull := Fintype.piFinset fun j : Fin n => Finset.range ((A.X N j) ^ 2)
  let Dtail := Fintype.piFinset fun i : T => Finset.range ((A.X N i.val) ^ 2)
  let Dcomp := Fintype.piFinset fun i : Tcomp => Finset.range ((A.X N i.val) ^ 2)
  let Dpair := Dtail ×ˢ Dcomp
  let e := piFinsetSplit T
  have hdisj : Disjoint T Tcomp := by
    apply Finset.disjoint_left.mpr
    intro i hiT hiC
    exact (Finset.mem_filter.mp hiC).2 hiT
  have hunion : T ∪ Tcomp = Finset.univ := by
    ext i
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      by_cases hi : i ∈ T
      · exact Finset.mem_union.mpr (Or.inl hi)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
  have hfullToPair (t : Fin n → ℕ) (ht : t ∈ Dfull) : e t ∈ Dpair := by
    apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hbound := (Fintype.mem_piFinset.mp ht) i.val
      rw [piFinsetSplit_left_apply T t i]
      exact hbound
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hbound := (Fintype.mem_piFinset.mp ht) i.val
      rw [piFinsetSplit_right_apply T t i]
      exact hbound
  have hpairToFull (z : (∀ i : T, ℕ) × (∀ i : Tcomp, ℕ))
      (hz : z ∈ Dpair) : e.symm z ∈ Dfull := by
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hj : j ∈ T
    · let i : T := ⟨j, hj⟩
      have htail := (Fintype.mem_piFinset.mp (Finset.mem_product.mp hz).1) i
      have hcoords := e.apply_symm_apply z
      have hcoord : e.symm z j = z.1 i := by
        calc
          e.symm z j = (e (e.symm z)).1 i :=
            (piFinsetSplit_left_apply T (e.symm z) i).symm
          _ = z.1 i := congrFun (congrArg Prod.fst hcoords) i
      rw [hcoord]
      exact htail
    · let i : Tcomp := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      have htail := (Fintype.mem_piFinset.mp (Finset.mem_product.mp hz).2) i
      have hcoords := e.apply_symm_apply z
      have hcoord : e.symm z j = z.2 i := by
        calc
          e.symm z j = (e (e.symm z)).2 i :=
            (piFinsetSplit_right_apply T (e.symm z) i).symm
          _ = z.2 i := congrFun (congrArg Prod.snd hcoords) i
      rw [hcoord]
      exact htail
  let fullTerm (t : Fin n → ℕ) :=
    (if (∏ j ∈ T, t j) = σ then 1 else 0) *
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)
  let splitTerm (z : (∀ i : T, ℕ) × (∀ i : Tcomp, ℕ)) :=
    (if (∏ i ∈ T.attach, z.1 i) = σ then 1 else 0) *
      ((∏ i ∈ T.attach,
          harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.1 i)) *
        ∏ i ∈ Tcomp.attach,
          harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.2 i))
  have hterm (t : Fin n → ℕ) (ht : t ∈ Dfull) : fullTerm t = splitTerm (e t) := by
    have htailProduct : (∏ j ∈ T, t j) = ∏ i ∈ T.attach, (e t).1 i := by
      calc
        (∏ j ∈ T, t j) = ∏ i ∈ T.attach, t i.val :=
          (Finset.prod_attach T fun j => t j).symm
        _ = ∏ i ∈ T.attach, (e t).1 i := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [← piFinsetSplit_left_apply T t i]
    have hmass :
        (∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
          (∏ i ∈ T.attach, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).1 i)) *
            ∏ i ∈ Tcomp.attach,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).2 i) := by
      calc
        (∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
            ∏ j ∈ Finset.univ,
              harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by simp
        _ = ∏ j ∈ T ∪ Tcomp,
              harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by rw [hunion]
        _ = (∏ j ∈ T,
              harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) *
            ∏ j ∈ Tcomp,
              harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) :=
            Finset.prod_union hdisj
        _ = (∏ i ∈ T.attach, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).1 i)) *
            ∏ i ∈ Tcomp.attach,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).2 i) := by
            have hmassT :
                (∏ j ∈ T, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
                  ∏ i ∈ T.attach,
                    harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).1 i) := by
              calc
                _ = ∏ i ∈ T.attach,
                    harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (t i.val) :=
                  (Finset.prod_attach T
                    (fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))).symm
                _ = _ := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  rw [← piFinsetSplit_left_apply T t i]
            have hmassC :
                (∏ j ∈ Tcomp, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
                  ∏ i ∈ Tcomp.attach,
                    harmonicNatLaw (A.X N i.val) (primorial (N + 1)) ((e t).2 i) := by
              calc
                _ = ∏ i ∈ Tcomp.attach,
                    harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (t i.val) :=
                  (Finset.prod_attach Tcomp
                    (fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))).symm
                _ = _ := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  rw [← piFinsetSplit_right_apply T t i]
            rw [hmassT, hmassC]
    dsimp [fullTerm, splitTerm]
    rw [htailProduct, hmass]
  have hsum : (∑ t ∈ Dfull, fullTerm t) = ∑ z ∈ Dpair, splitTerm z := by
    apply Finset.sum_bij (fun t _ => e t)
    · intro t ht
      exact hfullToPair t ht
    · intro t ht t' ht' hEq
      exact e.injective hEq
    · intro z hz
      exact ⟨e.symm z, hpairToFull z hz, e.apply_symm_apply z⟩
    · intro t ht
      exact hterm t ht
  rw [parameterTailProductLaw_eq_finite_sum A N T σ]
  exact hsum

theorem parameterTailProductLaw_eq_tailSubtype_sum {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ)
    (hX : ∀ j, 0 < A.X N j)
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) :
    FromArithmetic.parameterTailProductLaw A N T σ =
      ∑ u ∈ Fintype.piFinset
          (fun i : T => Finset.range ((A.X N i.val) ^ 2)),
        (if (∏ i : T, u i) = σ then 1 else 0) *
          ∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i) := by
  classical
  let Tcomp := finsetComplement T
  let Dtail := Fintype.piFinset fun i : T => Finset.range ((A.X N i.val) ^ 2)
  let Dcomp := Fintype.piFinset fun i : Tcomp => Finset.range ((A.X N i.val) ^ 2)
  have hcomp : (∑ v ∈ Dcomp,
      ∏ i : Tcomp, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (v i)) = 1 := by
    calc
      (∑ v ∈ Dcomp,
          ∏ i : Tcomp, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (v i)) =
        ∏ i : Tcomp,
          ∑ x ∈ Finset.range ((A.X N i.val) ^ 2),
            harmonicNatLaw (A.X N i.val) (primorial (N + 1)) x := by
              dsimp [Dcomp]
              symm
              exact Finset.prod_univ_sum
                (t := fun i : Tcomp => Finset.range ((A.X N i.val) ^ 2))
                (f := fun i x => harmonicNatLaw (A.X N i.val) (primorial (N + 1)) x)
      _ = ∏ i : Tcomp, 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact harmonicNatLaw_sum_range_eq_one _ _ (hX i.val) (hNorm i.val)
      _ = 1 := by simp
  have hsplit :
      (∑ z ∈ Dtail ×ˢ Dcomp,
        (if (∏ i : T, z.1 i) = σ then 1 else 0) *
          ((∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.1 i)) *
            ∏ i : Tcomp,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.2 i))) =
        ∑ u ∈ Dtail,
          (if (∏ i : T, u i) = σ then 1 else 0) *
            ∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i) := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    let I : ℝ := if (∏ i : T, u i) = σ then 1 else 0
    let M : ℝ := ∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i)
    calc
      (∑ v ∈ Dcomp,
        (if (∏ i : T, u i) = σ then 1 else 0) *
          ((∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i)) *
            ∏ i : Tcomp,
              harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (v i))) =
        ∑ v ∈ Dcomp, (I * M) *
          ∏ i : Tcomp, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (v i) := by
            apply Finset.sum_congr rfl
            intro v hv
            dsimp [I, M]
            ring
      _ = (I * M) *
          ∑ v ∈ Dcomp,
            ∏ i : Tcomp, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (v i) := by
              rw [Finset.mul_sum]
      _ = (if (∏ i : T, u i) = σ then 1 else 0) *
            ∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i) := by
              rw [hcomp]
              simp [I, M]
  calc
    FromArithmetic.parameterTailProductLaw A N T σ =
        ∑ z ∈ Dtail ×ˢ Dcomp,
          (if (∏ i : T, z.1 i) = σ then 1 else 0) *
            ((∏ i : T,
                harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.1 i)) *
              ∏ i : Tcomp,
                harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (z.2 i)) := by
          simpa [Dtail, Dcomp, Tcomp] using
            parameterTailProductLaw_eq_split_sum A N T σ
    _ = _ := hsplit

theorem harmonicLaw_summable (X W : ℕ) : Summable (harmonicLaw X W) := by
  classical
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  let T : Finset ℤ := Finset.image (fun n : ℕ => (n : ℤ)) S
  apply summable_of_ne_finset_zero (s := T)
  intro z hz
  by_contra hne
  have hcond : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W := by
    by_contra hnot
    have : harmonicLaw X W z = 0 := by simp [harmonicLaw, hnot]
    exact hne this
  have hnmem : z.toNat ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨hcond.2.1, hcond.2.2.1⟩, hcond.2.2.2⟩
  apply hz
  have hmem := Finset.mem_image_of_mem (fun n : ℕ => (n : ℤ)) hnmem
  rw [Int.toNat_of_nonneg hcond.1] at hmem
  exact hmem

theorem harmonicLaw_tsum_one_of_normalizer_pos (X W : ℕ) (hX : 0 < X)
    (hNorm : 0 < harmonicNormalizer X W) :
    ∑' z : ℤ, harmonicLaw X W z = 1 := by
  classical
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  let T : Finset ℤ := Finset.image (fun n : ℕ => (n : ℤ)) S
  have hzeroZ (z : ℤ) (hz : z ∉ T) : harmonicLaw X W z = 0 := by
    by_contra hne
    have hcond : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W := by
      by_contra hnot
      have : harmonicLaw X W z = 0 := by simp [harmonicLaw, hnot]
      exact hne this
    have hnmem : z.toNat ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨hcond.2.1, hcond.2.2.1⟩, hcond.2.2.2⟩
    apply hz
    have hmem := Finset.mem_image_of_mem (fun n : ℕ => (n : ℤ)) hnmem
    rw [Int.toNat_of_nonneg hcond.1] at hmem
    exact hmem
  have hzeroN (n : ℕ) (hn : n ∉ S) : harmonicNatLaw X W n = 0 := by
    by_contra hne
    have hcond : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W := by
      by_contra hnot
      have : harmonicNatLaw X W n = 0 := by simp [harmonicNatLaw, hnot]
      exact hne this
    exact hn (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hcond.1, hcond.2.1⟩, hcond.2.2⟩)
  have hNatSum : (∑ n ∈ S, harmonicNatLaw X W n) = 1 := by
    calc
      (∑ n ∈ S, harmonicNatLaw X W n) = ∑' n : ℕ, harmonicNatLaw X W n :=
        (tsum_eq_sum (s := S) hzeroN).symm
      _ = 1 := harmonicNatLaw_tsum_one_of_normalizer_pos X W hX hNorm
  calc
    (∑' z : ℤ, harmonicLaw X W z) = ∑ z ∈ T, harmonicLaw X W z :=
      tsum_eq_sum (s := T) hzeroZ
    _ = ∑ n ∈ S, harmonicNatLaw X W n := by
      symm
      refine Finset.sum_bij (s := S) (t := T)
        (f := harmonicNatLaw X W) (g := harmonicLaw X W)
        (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
      · intro n hn
        exact Finset.mem_image_of_mem _ hn
      · intro n hn z hz hEq
        exact Int.ofNat.inj hEq
      · intro z hz
        obtain ⟨n, hn, hEq⟩ := Finset.mem_image.mp hz
        exact ⟨n, hn, hEq⟩
      · intro n hn
        have hXn : X ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
        have hnX2 : n < X ^ 2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2
        simp [harmonicLaw, harmonicNatLaw, hXn, hnX2]
    _ = 1 := hNatSum

theorem parameterTailProductLaw_support_le {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hσ : parameterTailProductLaw A N T σ ≠ 0) :
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
  unfold parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem chainTail_support_le_masterScaleV {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (C : MasterChain n m) (d : Fin m) (σ : ℕ)
    (hσ : parameterTailProductLaw A N (C.block d).2.val σ ≠ 0) :
    σ ≤ masterScaleV A N C.gap := by
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
  have hmaster : (∏ j ∈ E, (A.X N j) ^ 2) ≤ masterScaleV A N C.gap := by
    dsimp [masterScaleV, E]
    omega
  exact (parameterTailProductLaw_support_le A N T σ hσ).trans (hprod_le.trans hmaster)

theorem harmonicNatLaw_nonneg_of_normalizer_pos (X W n : ℕ)
    (hNorm : 0 < harmonicNormalizer X W) : 0 ≤ harmonicNatLaw X W n := by
  by_cases h : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W
  · simp [harmonicNatLaw, h]
    positivity
  · simp [harmonicNatLaw, h]

theorem parameterTailProductLaw_nonneg {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n))
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) :
    ∀ σ, 0 ≤ parameterTailProductLaw A N T σ := by
  intro σ
  unfold parameterTailProductLaw
  apply tsum_nonneg
  intro t
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun j _ =>
      harmonicNatLaw_nonneg_of_normalizer_pos _ _ _ (hNorm j)

theorem parameterTailProductLaw_summable {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) :
    Summable (parameterTailProductLaw A N T) := by
  classical
  let Q := ∏ j ∈ T, (A.X N j) ^ 2
  apply summable_of_ne_finset_zero (s := Finset.range (Q + 1))
  intro σ hσ
  have hQlt : Q < σ := by
    have hnot : ¬ σ < Q + 1 := by simpa only [Finset.mem_range, not_lt] using hσ
    omega
  by_contra hne
  have hbound := parameterTailProductLaw_support_le A N T σ hne
  exact (not_le_of_gt (show Q < σ by simpa [Q] using hQlt)) hbound

theorem parameterTailProductLaw_tsum_one {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n))
    (hX : ∀ j, 0 < A.X N j)
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) :
    ∑' σ : ℕ, parameterTailProductLaw A N T σ = 1 := by
  classical
  let D : Finset (Fin n → ℕ) :=
    Fintype.piFinset fun j => Finset.range ((A.X N j) ^ 2)
  let Q := ∏ j ∈ T, (A.X N j) ^ 2
  have hrawZero (t : Fin n → ℕ) (ht : t ∉ D) :
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    have hnot : ¬ ∀ j, t j < (A.X N j) ^ 2 := by
      intro hall
      apply ht
      apply Fintype.mem_piFinset.mpr
      intro j
      simpa only [Finset.mem_range] using hall j
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero : harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
      have hlt : ¬ t j < (A.X N j) ^ 2 := by omega
      simp [harmonicNatLaw, hlt]
    exact Finset.prod_eq_zero (s := Finset.univ)
      (f := fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))
      (Finset.mem_univ j) hzero
  have hrawSum :
      (∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) = 1 := by
    calc
      (∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
          ∏ j, ∑ x ∈ Finset.range ((A.X N j) ^ 2),
            harmonicNatLaw (A.X N j) (primorial (N + 1)) x := by
        symm
        exact Finset.prod_univ_sum
          (t := fun j => Finset.range ((A.X N j) ^ 2))
          (f := fun j x => harmonicNatLaw (A.X N j) (primorial (N + 1)) x)
      _ = ∏ j, 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        have hnorm := harmonicNatLaw_tsum_one_of_normalizer_pos
          (A.X N j) (primorial (N + 1)) (hX j) (hNorm j)
        have hzero (x : ℕ) (hx : x ∉ Finset.range ((A.X N j) ^ 2)) :
            harmonicNatLaw (A.X N j) (primorial (N + 1)) x = 0 := by
          have hxlo : (A.X N j) ^ 2 ≤ x := by
            simpa only [Finset.mem_range, not_lt] using hx
          simp [harmonicNatLaw, hxlo]
        calc
          (∑ x ∈ Finset.range ((A.X N j) ^ 2),
              harmonicNatLaw (A.X N j) (primorial (N + 1)) x) =
              ∑' x : ℕ, harmonicNatLaw (A.X N j) (primorial (N + 1)) x :=
            (tsum_eq_sum (s := Finset.range ((A.X N j) ^ 2)) hzero).symm
          _ = 1 := hnorm
      _ = 1 := by simp
  have htailZero (σ : ℕ) (hσ : σ ∉ Finset.range (Q + 1)) :
      parameterTailProductLaw A N T σ = 0 := by
    have hQlt : Q < σ := by
      have hnot : ¬ σ < Q + 1 := by
        simpa only [Finset.mem_range, not_lt] using hσ
      omega
    by_contra hne
    have hbound := parameterTailProductLaw_support_le A N T σ hne
    exact (not_le_of_gt hQlt) (by simpa [Q] using hbound)
  have hinner (σ : ℕ) : parameterTailProductLaw A N T σ =
      ∑ t ∈ D,
        (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
    unfold parameterTailProductLaw
    apply tsum_eq_sum (s := D)
    intro t ht
    simp [hrawZero t ht]
  calc
    (∑' σ : ℕ, parameterTailProductLaw A N T σ) =
        ∑ σ ∈ Finset.range (Q + 1), parameterTailProductLaw A N T σ :=
      tsum_eq_sum (s := Finset.range (Q + 1)) htailZero
    _ = ∑ σ ∈ Finset.range (Q + 1),
        ∑ t ∈ D,
          (if (∏ j ∈ T, t j) = σ then 1 else 0) *
            ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hinner σ
    _ = ∑ t ∈ D, ∑ σ ∈ Finset.range (Q + 1),
        (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hprod_le : (∏ j ∈ T, t j) ≤ Q := by
        apply Finset.prod_le_prod
        intro j hj
        have hmem : t j ∈ Finset.range ((A.X N j) ^ 2) :=
          Fintype.mem_piFinset.mp ht j
        exact Nat.le_of_lt (Finset.mem_range.mp hmem)
      have hp : ∏ j ∈ T, t j ∈ Finset.range (Q + 1) := by
        simp only [Finset.mem_range]
        omega
      have hindicator :
          (∑ σ ∈ Finset.range (Q + 1),
            if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) = 1 := by
        calc
          (∑ σ ∈ Finset.range (Q + 1),
              if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) =
              (if (∏ j ∈ T, t j) = ∏ j ∈ T, t j then 1 else 0) := by
            apply Finset.sum_eq_single (∏ j ∈ T, t j)
            · intro σ hσ hne
              simp [eq_comm, hne]
            · intro hnot
              exact (hnot hp).elim
          _ = 1 := by simp
      calc
        (∑ σ ∈ Finset.range (Q + 1),
            (if (∏ j ∈ T, t j) = σ then 1 else 0) *
              ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
            (∑ σ ∈ Finset.range (Q + 1),
              if (∏ j ∈ T, t j) = σ then 1 else 0) *
              ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
          rw [Finset.sum_mul]
        _ = ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
          rw [hindicator]
          ring
    _ = 1 := hrawSum

noncomputable def divisorTemplateOfFinset {n b : ℕ} (T : Finset (Fin n))
    (hT : T.card ≤ b) : DivisorTemplate n b where
  arity := T.card
  arity_le := hT
  cutoff i := (T.orderIsoOfFin rfl i).val

theorem divisorTemplateOfFinset_cutoff_mem {n b : ℕ} (T : Finset (Fin n))
    (hT : T.card ≤ b) (i : Fin (T.card)) :
    (divisorTemplateOfFinset T hT).cutoff i ∈ T := (T.orderIsoOfFin rfl i).property

theorem parameterTailProductLaw_eq_divisorTemplateLaw_ofFinset {n b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (hT : T.card ≤ b)
    (hX : ∀ j, 0 < A.X N j)
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1)))
    (σ : ℕ) :
    parameterTailProductLaw A N T σ =
      divisorTemplateLaw A N (divisorTemplateOfFinset T hT) σ := by
  classical
  let D := divisorTemplateOfFinset T hT
  let ord : Fin T.card ≃ T := (T.orderIsoOfFin rfl).toEquiv
  let ePi : (Fin T.card → ℕ) ≃ (∀ i : T, ℕ) :=
    Equiv.piCongrLeft' (fun _ : Fin T.card => ℕ) ord
  let Dsub := Fintype.piFinset
    (fun i : T => Finset.range ((A.X N i.val) ^ 2))
  let Dfin := Fintype.piFinset
    (fun i : Fin T.card => Finset.range ((A.X N (D.cutoff i)) ^ 2))
  have hmem (w : Fin T.card → ℕ) : w ∈ Dfin ↔ ePi w ∈ Dsub := by
    constructor
    · intro hw
      apply Fintype.mem_piFinset.mpr
      intro j
      let i := ord.symm j
      have hi := (Fintype.mem_piFinset.mp hw) i
      have hcut : D.cutoff i = j.val := by
        change (ord (ord.symm j)).val = j.val
        exact congrArg Subtype.val (ord.apply_symm_apply j)
      have hfun : ePi w j = w i := by
        simp [ePi, i, Equiv.piCongrLeft']
      simpa [hcut, hfun] using hi
    · intro hu
      apply Fintype.mem_piFinset.mpr
      intro i
      have hi := (Fintype.mem_piFinset.mp hu) (ord i)
      have hcut : D.cutoff i = (ord i).val := by rfl
      have hfun : ePi w (ord i) = w i := by
        simp [ePi, Equiv.piCongrLeft']
      simpa [hcut, hfun] using hi
  have hprod (w : Fin T.card → ℕ) :
      (∏ j : T, (ePi w) j) = ∏ i : Fin T.card, w i := by
    symm
    exact Fintype.prod_equiv ord (fun i => w i) (fun j => (ePi w) j) (by
      intro i
      simp [ePi, Equiv.piCongrLeft'])
  have hmass (w : Fin T.card → ℕ) :
      (∏ j : T,
        harmonicNatLaw (A.X N j.val) (primorial (N + 1)) ((ePi w) j)) =
        ∏ i : Fin T.card,
          harmonicNatLaw (A.X N (D.cutoff i)) (primorial (N + 1)) (w i) := by
    symm
    exact Fintype.prod_equiv ord
      (fun i => harmonicNatLaw (A.X N (D.cutoff i))
        (primorial (N + 1)) (w i))
      (fun j => harmonicNatLaw (A.X N j.val)
        (primorial (N + 1)) ((ePi w) j))
      (by
        intro i
        have hcut : D.cutoff i = (ord i).val := rfl
        have heval : ePi w (ord i) = w i := by
          simp [ePi, Equiv.piCongrLeft']
        rw [hcut, heval])
  let subTerm (u : ∀ i : T, ℕ) :=
    (if (∏ i : T, u i) = σ then 1 else 0) *
      ∏ i : T, harmonicNatLaw (A.X N i.val) (primorial (N + 1)) (u i)
  let finTerm (w : Fin T.card → ℕ) :=
    (if (∏ i, w i) = σ then 1 else 0) *
      ∏ i, harmonicNatLaw (A.X N (D.cutoff i)) (primorial (N + 1)) (w i)
  have hbij :
      (∑ w ∈ Dfin, finTerm w) = ∑ u ∈ Dsub, subTerm u := by
    apply Finset.sum_bij (fun w _ => ePi w)
    · intro w hw
      exact (hmem w).mp hw
    · intro w hw w' hw' hEq
      exact ePi.injective hEq
    · intro u hu
      refine ⟨ePi.symm u, ?_, ePi.apply_symm_apply u⟩
      exact (hmem (ePi.symm u)).mpr (by simpa using hu)
    · intro w hw
      simp only [subTerm, finTerm, hprod w, hmass w]
      by_cases h : (∏ i, w i) = σ <;> simp [h]
      rfl
  have hsub := parameterTailProductLaw_eq_tailSubtype_sum A N T σ hX hNorm
  have hfin := harmonicProductLaw_eq_finite_sum (primorial (N + 1))
    (fun i => A.X N (D.cutoff i)) σ
  calc
    parameterTailProductLaw A N T σ = ∑ u ∈ Dsub, subTerm u := by
      simpa [Dsub, subTerm] using hsub
    _ = ∑ w ∈ Dfin, finTerm w := hbij.symm
    _ = harmonicProductLaw (primorial (N + 1))
        (fun i => A.X N (D.cutoff i)) σ := by
      change (∑ w ∈ Fintype.piFinset
          (fun i : Fin T.card => Finset.range ((A.X N (D.cutoff i)) ^ 2)),
          (if (∏ i, w i) = σ then 1 else 0) *
            ∏ i, harmonicNatLaw (A.X N (D.cutoff i))
              (primorial (N + 1)) (w i)) = _
      exact hfin.symm
    _ = divisorTemplateLaw A N D σ := by rfl

theorem parameterTailProductLaw_support_pos {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hX : ∀ j, 0 < A.X N j)
    (hσ : parameterTailProductLaw A N T σ ≠ 0) : 1 ≤ σ := by
  by_contra hnot
  have hσzero : σ = 0 := by omega
  have hterm (t : Fin n → ℕ) :
      (if (∏ j ∈ T, t j) = σ then 1 else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    by_cases hall : ∀ j ∈ T, 0 < t j
    · have hprod : 0 < ∏ j ∈ T, t j := Finset.prod_pos hall
      simp [hσzero, Nat.ne_of_gt hprod]
    · push_neg at hall
      obtain ⟨j, hjT, hj⟩ := hall
      have hjnot : ¬ 0 < t j := by omega
      have hj0 : t j = 0 := Nat.eq_zero_of_not_pos hjnot
      have hfactor :
          harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
        have hnotX : ¬ A.X N j ≤ t j := by
          rw [hj0]
          exact Nat.not_le_of_gt (hX j)
        simp [harmonicNatLaw, hnotX]
      have hmass :
          (∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) = 0 :=
        Finset.prod_eq_zero (s := Finset.univ)
          (f := fun k => harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k))
          (Finset.mem_univ j) hfactor
      simp [hσzero, hmass]
  apply hσ
  unfold parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem chainWeight_le_masterScaleV_of_normalizers {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (C : MasterChain n m) (d : Fin m)
    (hX : ∀ j, 0 < A.X N j)
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) (y : ℤ) :
    nuB (parameterTailProductLaw A N (C.block d).2.val) y ≤
      (masterScaleV A N C.gap : ℝ) := by
  apply nuB_le_of_probability_support
    (tailLaw := parameterTailProductLaw A N (C.block d).2.val)
    (V := masterScaleV A N C.gap) (y := y)
  · exact parameterTailProductLaw_nonneg A N (C.block d).2.val hNorm
  · exact parameterTailProductLaw_summable A N (C.block d).2.val
  · exact parameterTailProductLaw_tsum_one A N (C.block d).2.val hX hNorm
  · intro σ hσ
    have hσbound := chainTail_support_le_masterScaleV A N C d σ hσ
    exact_mod_cast hσbound

theorem chainWeight_le_masterScaleV {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (y : ℤ) :
    chainWeight S.core.parameters C N d y ≤
      (masterScaleV S.core.parameters N C.gap : ℝ) := by
  apply chainWeight_le_masterScaleV_of_normalizers S.core.parameters N C d
  · exact S.core.parameters.Xpos N
  · intro j
    exact harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N j)

theorem chainWeight_nonneg {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (y : ℤ) :
    0 ≤ chainWeight S.core.parameters C N d y := by
  change 0 ≤ nuB (parameterTailProductLaw S.core.parameters N (C.block d).2.val) y
  unfold nuB
  apply tsum_nonneg
  intro σ
  apply mul_nonneg
  · apply mul_nonneg
    · exact parameterTailProductLaw_nonneg S.core.parameters N (C.block d).2.val
        (fun j => harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
          (S.gapStage.valid_raw_cutoffs N j)) σ
    · exact Nat.cast_nonneg σ
  · split_ifs <;> norm_num

theorem chainWeight_support {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (σ : ℕ)
    (hσ : parameterTailProductLaw S.core.parameters N (C.block d).2.val σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ masterScaleV S.core.parameters N C.gap := by
  constructor
  · exact parameterTailProductLaw_support_pos S.core.parameters N (C.block d).2.val σ
      (fun j => S.core.parameters.Xpos N j) hσ
  · exact chainTail_support_le_masterScaleV S.core.parameters N C d σ hσ

def primePoolSupport (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter Nat.Prime

private theorem primePoolLaw_zero_of_not_mem_support (lo hi p : ℕ)
    (hp : p ∉ primePoolSupport lo hi) : primePoolLaw lo hi p = 0 := by
  by_contra hne
  have hcond : lo ≤ p ∧ p < hi ∧ p.Prime := by
    by_contra hnot
    have : primePoolLaw lo hi p = 0 := by simp [primePoolLaw, hnot]
    exact hne this
  apply hp
  simp [primePoolSupport, Finset.mem_filter, Finset.mem_Ico, hcond]

theorem primePoolLaw_nonneg (lo hi p : ℕ) (hMass : 0 < primePoolMass lo hi) :
    0 ≤ primePoolLaw lo hi p := by
  by_cases h : lo ≤ p ∧ p < hi ∧ p.Prime
  · simp [primePoolLaw, h]
    positivity
  · simp [primePoolLaw, h]

theorem primePoolLaw_summable (lo hi : ℕ) : Summable (primePoolLaw lo hi) := by
  apply summable_of_ne_finset_zero (s := primePoolSupport lo hi)
  intro p hp
  exact primePoolLaw_zero_of_not_mem_support lo hi p hp

theorem primePoolLaw_tsum_one (lo hi : ℕ) (hMass : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  classical
  let S := primePoolSupport lo hi
  have hzero (p : ℕ) (hp : p ∉ S) : primePoolLaw lo hi p = 0 :=
    primePoolLaw_zero_of_not_mem_support lo hi p hp
  have hterm (p : ℕ) (hp : p ∈ S) :
      primePoolLaw lo hi p = (1 / (p : ℝ)) / primePoolMass lo hi := by
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hprime⟩
    rcases Finset.mem_Ico.mp hpIco with ⟨hlo, hhi⟩
    simp [primePoolLaw, hlo, hhi, hprime]
  calc
    (∑' p : ℕ, primePoolLaw lo hi p) = ∑ p ∈ S, primePoolLaw lo hi p :=
      tsum_eq_sum (s := S) hzero
    _ = (∑ p ∈ S, 1 / (p : ℝ)) / primePoolMass lo hi := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ = 1 := by
      have hsum : (∑ p ∈ S, 1 / (p : ℝ)) = primePoolMass lo hi := rfl
      rw [hsum]
      exact div_self hMass.ne'

theorem primePoolLaw_secondMoment (lo hi : ℕ) (hMass : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, (p : ℝ) * (primePoolLaw lo hi p) ^ 2 =
      (primePoolMass lo hi)⁻¹ := by
  classical
  let S := primePoolSupport lo hi
  have hzero (p : ℕ) (hp : p ∉ S) :
      (p : ℝ) * (primePoolLaw lo hi p) ^ 2 = 0 := by
    simp [primePoolLaw_zero_of_not_mem_support lo hi p hp]
  have hterm (p : ℕ) (hp : p ∈ S) :
      (p : ℝ) * (primePoolLaw lo hi p) ^ 2 =
        (1 / (p : ℝ)) / (primePoolMass lo hi) ^ 2 := by
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hprime⟩
    rcases Finset.mem_Ico.mp hpIco with ⟨hlo, hhi⟩
    have hpPos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hprime.pos
    unfold primePoolLaw
    rw [if_pos ⟨hlo, hhi, hprime⟩]
    field_simp [hpPos.ne', hMass.ne']
  calc
    (∑' p : ℕ, (p : ℝ) * (primePoolLaw lo hi p) ^ 2) =
        ∑ p ∈ S, (p : ℝ) * (primePoolLaw lo hi p) ^ 2 :=
      tsum_eq_sum (s := S) hzero
    _ = (∑ p ∈ S, 1 / (p : ℝ)) / (primePoolMass lo hi) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ = (primePoolMass lo hi)⁻¹ := by
      have hsum : (∑ p ∈ S, 1 / (p : ℝ)) = primePoolMass lo hi := rfl
      rw [hsum]
      field_simp [hMass.ne']

theorem primePoolMass_tendsto_atTop {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm) (l : Fin K) :
    Tendsto (fun N => primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hdom := S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)
  have hratio : ∀ᶠ N in atTop,
      max b 0 + 1 < primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper / (masterScaleV S.core.parameters N l : ℝ) := by
    simpa using hdom.eventually_gt_atTop (max b 0 + 1)
  filter_upwards [hratio] with N hN
  have hV : 1 ≤ (masterScaleV S.core.parameters N l : ℝ) := by
    have hNat : 2 ≤ masterScaleV S.core.parameters N l := by
      unfold masterScaleV
      omega
    have hNatReal : (2 : ℝ) ≤ (masterScaleV S.core.parameters N l : ℝ) := by
      exact_mod_cast hNat
    linarith
  have hVpos : (0 : ℝ) < (masterScaleV S.core.parameters N l : ℝ) := by
    linarith
  have hmul : (max b 0 + 1) * (masterScaleV S.core.parameters N l : ℝ) <
      primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper :=
    (lt_div_iff₀ hVpos).mp hN
  have hb : b < (max b 0 + 1) * (masterScaleV S.core.parameters N l : ℝ) := by
    have hbmax : b ≤ max b 0 := le_max_left _ _
    have hA : 0 ≤ max b 0 + 1 := by positivity
    have hAprod : max b 0 + 1 ≤
        (max b 0 + 1) * (masterScaleV S.core.parameters N l : ℝ) := by
      calc
        max b 0 + 1 = (max b 0 + 1) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hV hA
    linarith
  exact le_of_lt (hb.trans hmul)

theorem primePoolMass_nonneg (lo hi : ℕ) : 0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  apply Finset.sum_nonneg
  intro p hp
  exact one_div_nonneg.mpr (Nat.cast_nonneg p)

theorem primePoolMass_inverse_superpolynomial {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm) (l : Fin K) :
    SuperPolynomialSmall
      (fun N => (primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper)⁻¹)
      (fun N => (masterScaleV S.core.parameters N l : ℝ)) := by
  intro A hA
  have hVge : ∀ N, 1 ≤ (masterScaleV S.core.parameters N l : ℝ) := by
    intro N
    have hNat : 2 ≤ masterScaleV S.core.parameters N l := by
      unfold masterScaleV
      omega
    have hNatReal : (2 : ℝ) ≤ (masterScaleV S.core.parameters N l : ℝ) := by
      exact_mod_cast hNat
    linarith
  have hMassTop := primePoolMass_tendsto_atTop S l
  have hMassPos : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper :=
    hMassTop.eventually_gt_atTop 0
  have hDom := S.primeStage.pool_harmonic_mass_dominates l (A + 1) (by linarith)
  have hInv : Tendsto
      ((fun r : ℝ => r⁻¹) ∘ fun N =>
        primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper /
          (masterScaleV S.core.parameters N l : ℝ) ^ (A + 1))
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hDom
  have hnonneg : ∀ N, 0 ≤
      (primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper)⁻¹ *
        (masterScaleV S.core.parameters N l : ℝ) ^ A := by
    intro N
    apply mul_nonneg
    · exact inv_nonneg.mpr (primePoolMass_nonneg _ _)
    · exact Real.rpow_nonneg (by positivity) A
  have hle : ∀ᶠ N in atTop,
      (primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper)⁻¹ *
        (masterScaleV S.core.parameters N l : ℝ) ^ A ≤
      (fun r : ℝ => r⁻¹)
        (primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper /
          (masterScaleV S.core.parameters N l : ℝ) ^ (A + 1)) := by
    filter_upwards [hMassPos] with N hM
    let V : ℝ := masterScaleV S.core.parameters N l
    let M : ℝ := primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper
    have hV1 : 1 ≤ V := hVge N
    have hVp : 0 < V := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hV1
    have hMp : 0 < M := hM
    have hVa : 0 ≤ V ^ A := Real.rpow_nonneg hVp.le A
    have hRpow : V ^ (A + 1) = V ^ A * V := by
      rw [Real.rpow_add hVp]
      simp
    have hrecip : (fun r : ℝ => r⁻¹) (M / V ^ (A + 1)) = (V ^ A / M) * V := by
      rw [hRpow]
      field_simp [hMp.ne', hVp.ne']
    change M⁻¹ * V ^ A ≤ (M / V ^ (A + 1))⁻¹
    have hleft : M⁻¹ * V ^ A = V ^ A / M := by
      field_simp [hMp.ne']
    rw [hleft]
    change V ^ A / M ≤ (fun r : ℝ => r⁻¹) (M / V ^ (A + 1))
    rw [hrecip]
    calc
      V ^ A / M = (V ^ A / M) * 1 := by ring
      _ ≤ (V ^ A / M) * V :=
        mul_le_mul_of_nonneg_left hV1 (div_nonneg hVa hMp.le)
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hle hInv

noncomputable def independentPrimePoolSupport {q : ℕ} (lo hi : Fin q → ℕ) :
    Finset (Fin q → ℕ) :=
  Fintype.piFinset fun i => primePoolSupport (lo i) (hi i)

private theorem independentPrimePoolMass_zero_of_not_mem_support {q : ℕ}
    (lo hi : Fin q → ℕ) (p : Fin q → ℕ)
    (hp : p ∉ independentPrimePoolSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  have hnot : ¬ ∀ i, p i ∈ primePoolSupport (lo i) (hi i) := by
    intro hall
    apply hp
    exact Fintype.mem_piFinset.mpr hall
  obtain ⟨i, hnotCoord⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  exact Finset.prod_eq_zero (s := Finset.univ)
    (f := fun i => primePoolLaw (lo i) (hi i) (p i)) (Finset.mem_univ i)
    (primePoolLaw_zero_of_not_mem_support (lo i) (hi i) (p i) hnotCoord)

theorem independentPrimePoolMass_summable {q : ℕ} (lo hi : Fin q → ℕ) :
    Summable (independentPrimePoolMass lo hi) := by
  classical
  apply summable_of_ne_finset_zero (s := independentPrimePoolSupport lo hi)
  intro p hp
  exact independentPrimePoolMass_zero_of_not_mem_support lo hi p hp

theorem independentPrimePoolMass_tsum_one {q : ℕ} (lo hi : Fin q → ℕ)
    (hMass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    ∑' p : Fin q → ℕ, independentPrimePoolMass lo hi p = 1 := by
  classical
  let D := independentPrimePoolSupport lo hi
  have hzero (p : Fin q → ℕ) (hp : p ∉ D) :
      independentPrimePoolMass lo hi p = 0 :=
    independentPrimePoolMass_zero_of_not_mem_support lo hi p hp
  have hcoord (i : Fin q) :
      (∑ p ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) p) = 1 := by
    calc
      (∑ p ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) p) =
          ∑' p : ℕ, primePoolLaw (lo i) (hi i) p := by
        symm
        apply tsum_eq_sum
        intro p hp
        exact primePoolLaw_zero_of_not_mem_support (lo i) (hi i) p hp
      _ = 1 := primePoolLaw_tsum_one (lo i) (hi i) (hMass i)
  have hfinite : (∑ p ∈ D, independentPrimePoolMass lo hi p) = 1 := by
    calc
      (∑ p ∈ D, independentPrimePoolMass lo hi p) =
          ∏ i, ∑ x ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) x := by
        unfold D independentPrimePoolSupport independentPrimePoolMass
        symm
        exact Finset.prod_univ_sum
          (t := fun i => primePoolSupport (lo i) (hi i))
          (f := fun i p => primePoolLaw (lo i) (hi i) p)
      _ = ∏ i, 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hcoord i
      _ = 1 := by simp
  calc
    (∑' p : Fin q → ℕ, independentPrimePoolMass lo hi p) =
        ∑ p ∈ D, independentPrimePoolMass lo hi p :=
      tsum_eq_sum (s := D) hzero
    _ = 1 := hfinite

theorem independentPrimePoolBadAverage_le {q : ℕ} (lo hi : Fin q → ℕ)
    (hMass : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (E : (Fin q → ℕ) → Prop) (F : (Fin q → ℕ) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ p, |F p| ≤ B) :
    |∑' p : Fin q → ℕ, independentPrimePoolMass lo hi p *
        (if E p then F p else 0)| ≤
      B * independentPrimePoolProbability lo hi E := by
  classical
  let D := independentPrimePoolSupport lo hi
  have htermZero (p : Fin q → ℕ) (hp : p ∉ D) :
      independentPrimePoolMass lo hi p * (if E p then F p else 0) = 0 := by
    simp [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp]
  have hprobZero (p : Fin q → ℕ) (hp : p ∉ D) :
      independentPrimePoolMass lo hi p * (if E p then 1 else 0) = 0 := by
    simp [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp]
  have hprob : independentPrimePoolProbability lo hi E =
      ∑ p ∈ D, independentPrimePoolMass lo hi p * (if E p then 1 else 0) := by
    change (∑' p : Fin q → ℕ,
      independentPrimePoolMass lo hi p * (if E p then 1 else 0)) = _
    exact tsum_eq_sum (s := D) hprobZero
  have hbound :
      (∑ p ∈ D,
        |independentPrimePoolMass lo hi p * (if E p then F p else 0)|) ≤
        ∑ p ∈ D,
          independentPrimePoolMass lo hi p * (if E p then B else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    have hμ : 0 ≤ independentPrimePoolMass lo hi p := by
      unfold independentPrimePoolMass
      apply Finset.prod_nonneg
      intro i _
      exact primePoolLaw_nonneg (lo i) (hi i) (p i) (hMass i)
    by_cases hEp : E p
    · simp only [if_pos hEp, abs_mul, abs_of_nonneg hμ]
      exact mul_le_mul_of_nonneg_left (hF p) hμ
    · simp [hEp]
  calc
    |∑' p : Fin q → ℕ,
        independentPrimePoolMass lo hi p * (if E p then F p else 0)| =
      |∑ p ∈ D,
        independentPrimePoolMass lo hi p * (if E p then F p else 0)| := by
          rw [tsum_eq_sum (s := D) htermZero]
    _ ≤ ∑ p ∈ D,
        |independentPrimePoolMass lo hi p * (if E p then F p else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ D,
        independentPrimePoolMass lo hi p * (if E p then B else 0) := hbound
    _ = B * independentPrimePoolProbability lo hi E := by
      rw [hprob]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hEp : E p <;> simp [hEp, mul_comm]

theorem independentPrimePoolBadAverage_tendsto_zero {q : ℕ}
    (lo hi : ℕ → Fin q → ℕ) (E : ℕ → (Fin q → ℕ) → Prop)
    (F : ℕ → (Fin q → ℕ) → ℝ) (e V : ℕ → ℝ) (A : ℝ)
    (hMass : ∀ᶠ N in atTop, ∀ i, 0 < primePoolMass (lo N i) (hi N i))
    (hsmall : SuperPolynomialSmall e V)
    (hV : ∀ᶠ N in atTop, 1 ≤ V N)
    (hProb : ∀ᶠ N in atTop,
      independentPrimePoolProbability (lo N) (hi N) (E N) ≤ e N)
    (hF : ∀ N p, |F N p| ≤ V N ^ A) :
    Tendsto (fun N =>
      |∑' p : Fin q → ℕ,
        independentPrimePoolMass (lo N) (hi N) p * (if E N p then F N p else 0)|)
      atTop (nhds 0) := by
  classical
  have hprobNonneg (N : ℕ) (hMN : ∀ i, 0 < primePoolMass (lo N i) (hi N i)) :
      0 ≤ independentPrimePoolProbability (lo N) (hi N) (E N) := by
    unfold independentPrimePoolProbability
    apply tsum_nonneg
    intro p
    have hμ : 0 ≤ independentPrimePoolMass (lo N) (hi N) p := by
      unfold independentPrimePoolMass
      apply Finset.prod_nonneg
      intro i _
      exact primePoolLaw_nonneg (lo N i) (hi N i) (p i) (hMN i)
    by_cases hp : E N p
    · simp [hp, hμ]
    · simp [hp]
  have he : ∀ᶠ N in atTop, 0 ≤ e N := by
    filter_upwards [hMass, hProb] with N hMN hP
    exact (hprobNonneg N hMN).trans hP
  have hsmallPow := hsmall.mul_rpow_tendsto he hV A
  have hbound : ∀ᶠ N in atTop,
      |∑' p : Fin q → ℕ,
        independentPrimePoolMass (lo N) (hi N) p * (if E N p then F N p else 0)| ≤
        e N * V N ^ A := by
    filter_upwards [hMass, hV, hProb] with N hMN hVN hP
    have hB : 0 ≤ V N ^ A := Real.rpow_nonneg (by linarith) A
    calc
      |∑' p : Fin q → ℕ,
          independentPrimePoolMass (lo N) (hi N) p * (if E N p then F N p else 0)| ≤
        V N ^ A * independentPrimePoolProbability (lo N) (hi N) (E N) :=
          independentPrimePoolBadAverage_le (lo N) (hi N) hMN (E N) (F N)
            (V N ^ A) hB (hF N)
      _ ≤ e N * V N ^ A := by
        calc
          V N ^ A * independentPrimePoolProbability (lo N) (hi N) (E N) =
              independentPrimePoolProbability (lo N) (hi N) (E N) * V N ^ A := by ring
          _ ≤ e N * V N ^ A := mul_le_mul_of_nonneg_right hP hB
  have habs : ∀ N, 0 ≤
      |∑' p : Fin q → ℕ,
        independentPrimePoolMass (lo N) (hi N) p * (if E N p then F N p else 0)| :=
    fun _ => abs_nonneg _
  exact squeeze_zero' (Filter.Eventually.of_forall habs) hbound hsmallPow

theorem primePoolMass_pos_eventually {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop, 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper := by
  have hdom := S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)
  have hlarge : ∀ᶠ N in atTop,
      1 < primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper /
        (masterScaleV S.core.parameters N l : ℝ) := by
    simpa using hdom.eventually_gt_atTop 1
  filter_upwards [hlarge] with N hN
  have hV : 0 < (masterScaleV S.core.parameters N l : ℝ) := by
    dsimp [masterScaleV]
    positivity
  have hlt : (masterScaleV S.core.parameters N l : ℝ) <
      primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper :=
    by simpa using (lt_div_iff₀ hV).mp hN
  exact hV.trans hlt

theorem gapSlotMass_summable {K s q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (l : Fin K) (N : ℕ) :
    Summable (gapSlotMass S l N : (Fin q → ℕ) → ℝ) := by
  classical
  unfold gapSlotMass
  exact independentPrimePoolMass_summable
    (fun _ : Fin q => (S.primeStage.pool N l).lower)
    (fun _ : Fin q => (S.primeStage.pool N l).upper)

theorem gapSlotMass_tsum_one {K s q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (l : Fin K) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper) :
    ∑' p : Fin q → ℕ, gapSlotMass S l N p = 1 := by
  classical
  unfold gapSlotMass
  exact independentPrimePoolMass_tsum_one
    (fun _ : Fin q => (S.primeStage.pool N l).lower)
    (fun _ : Fin q => (S.primeStage.pool N l).upper) (fun _ => hMass)

theorem chainWeight_mul_eq_of_prime_gt {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (p : ℕ)
    (hp : p.Prime) (hV : masterScaleV S.core.parameters N C.gap < p) (y : ℤ) :
    chainWeight S.core.parameters C N d ((p : ℤ) * y) =
      chainWeight S.core.parameters C N d y := by
  change nuB (parameterTailProductLaw S.core.parameters N (C.block d).2.val) ((p : ℤ) * y) =
    nuB (parameterTailProductLaw S.core.parameters N (C.block d).2.val) y
  apply nuB_mul_eq_of_prime_gt_support _ p (masterScaleV S.core.parameters N C.gap)
    hp hV
  intro σ hσ
  exact chainWeight_support S C N d σ hσ

theorem chainWeight_div_eq_of_prime_gt {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (p : ℕ)
    (hp : p.Prime) (hV : masterScaleV S.core.parameters N C.gap < p) (y : ℤ)
    (hdiv : (p : ℤ) ∣ y) :
    chainWeight S.core.parameters C N d (y / (p : ℤ)) =
      chainWeight S.core.parameters C N d y := by
  change nuB (parameterTailProductLaw S.core.parameters N (C.block d).2.val)
      (y / (p : ℤ)) =
    nuB (parameterTailProductLaw S.core.parameters N (C.block d).2.val) y
  apply nuB_div_eq_of_prime_gt_support _ p (masterScaleV S.core.parameters N C.gap)
    hp hV
  · intro σ hσ
    exact chainWeight_support S C N d σ hσ
  · exact hdiv

theorem chainWeight_rat_div_mul_eq_of_prime_gt {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (p₀ p₁ : ℕ)
    (hp₀ : p₀.Prime) (hp₁ : p₁.Prime)
    (hV₀ : masterScaleV S.core.parameters N C.gap < p₀)
    (hV₁ : masterScaleV S.core.parameters N C.gap < p₁)
    (hne : p₀ ≠ p₁) (y : ℤ)
    (hden : (((p₀ : ℚ) / (p₁ : ℚ)) * (y : ℚ)).den = 1) :
    chainWeight S.core.parameters C N d
        ((((p₀ : ℚ) / (p₁ : ℚ)) * (y : ℚ)).num) =
      chainWeight S.core.parameters C N d y := by
  let x : ℚ := ((p₀ : ℚ) / (p₁ : ℚ)) * (y : ℚ)
  have hp₁cast : (p₁ : ℚ) ≠ 0 := by exact_mod_cast hp₁.pos.ne'
  have hxnum : (x.num : ℚ) = x := (Rat.den_eq_one_iff x).mp (by simpa [x] using hden)
  have hcross : (p₁ : ℚ) * (x.num : ℚ) = (p₀ : ℚ) * (y : ℚ) := by
    rw [hxnum]
    dsimp [x]
    field_simp [hp₁cast]
  have hcrossInt : (p₁ : ℤ) * x.num = (p₀ : ℤ) * y := by
    exact_mod_cast hcross
  have hnotdvd : ¬ p₁ ∣ p₀ := by
    intro hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq hp₁ hp₀).mp hdvd
    exact hne heq.symm
  have hcop : Nat.Coprime p₁ p₀ := (hp₁.coprime_iff_not_dvd).2 hnotdvd
  have hcopInt : Int.gcd (p₁ : ℤ) (p₀ : ℤ) = 1 := by
    have hgcd := Nat.coprime_iff_gcd_eq_one.mp hcop
    exact_mod_cast hgcd
  have hdivProd : (p₁ : ℤ) ∣ (p₀ : ℤ) * y := by
    refine ⟨x.num, ?_⟩
    exact hcrossInt.symm
  have hdiv : (p₁ : ℤ) ∣ y :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hdivProd hcopInt
  let n : ℤ := (p₀ : ℤ) * (y / (p₁ : ℤ))
  have hratEq : (n : ℚ) = x := by
    calc
      (n : ℚ) = (p₀ : ℚ) * ((y / (p₁ : ℤ) : ℤ) : ℚ) := by simp [n]
      _ = (p₀ : ℚ) * ((y : ℚ) / (p₁ : ℚ)) := by
        exact congrArg (fun t : ℚ => (p₀ : ℚ) * t) (Int.cast_div hdiv hp₁cast)
      _ = x := by
        dsimp [x]
        field_simp [hp₁cast]
  have hnum : x.num = n := by
    have h := congrArg Rat.num hratEq
    simpa only [Rat.num_intCast] using h.symm
  rw [show (((p₀ : ℚ) / (p₁ : ℚ)) * (y : ℚ)).num = n by simpa [x] using hnum]
  calc
    chainWeight S.core.parameters C N d n =
        chainWeight S.core.parameters C N d (y / (p₁ : ℤ)) := by
          dsimp [n]
          exact chainWeight_mul_eq_of_prime_gt S C N d p₀ hp₀ hV₀
            (y / (p₁ : ℤ))
    _ = chainWeight S.core.parameters C N d y :=
          chainWeight_div_eq_of_prime_gt S C N d p₁ hp₁ hV₁ y hdiv

theorem chainScale_ratio_den_one_eventually {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ J : Finset (Fin m), ∀ (hJ : J.Nonempty) k, k ∈ J →
      (chainScale S.core.parameters C a N k /
        chainScale S.core.parameters C a N (J.max' hJ)).den = 1 := by
  filter_upwards [S.core.chain_coefficients] with N hN
  obtain ⟨c, hcEq, hcPos, hcDiv⟩ := hN m C a ha
  intro J hJ k hk
  let d := J.max' hJ
  have hscale (j : Fin m) : chainScale S.core.parameters C a N j = (c j : ℚ) := by
    exact (hcEq j).symm
  have hdpos : c d ≠ 0 := (hcPos d).ne'
  by_cases hkd : k = d
  · subst k
    rw [hscale d]
    have hdne : (c d : ℚ) ≠ 0 := by exact_mod_cast hdpos
    rw [div_self hdne]
    simp
  · have hle : k ≤ d := Finset.le_max' J k hk
    have hlt : k < d := lt_of_le_of_ne hle hkd
    obtain ⟨n, hn⟩ := hcDiv k d hlt
    have hratio : (c k : ℚ) / (c d : ℚ) =
        (primorial (N + 1) : ℚ) * (n : ℚ) := by
      rw [hn]
      have hdne : (c d : ℚ) ≠ 0 := by exact_mod_cast hdpos
      field_simp [hdne]
      push_cast
      ring
    rw [hscale k, hscale d, hratio]
    rw [← Nat.cast_mul]
    exact Rat.den_natCast _

theorem chainScale_num_coprime_of_prime_gt_eventually {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ d r, r.Prime → N + 1 < r →
      Nat.Coprime (chainScale S.core.parameters C a N d).num.natAbs r := by
  filter_upwards [S.core.chain_coefficients, S.gapStage.coefficient_divides_modulus]
    with N hcoeff hdiv
  obtain ⟨c, hcEq, hcPos, _⟩ := hcoeff m C a ha
  have hcRel : ∀ d, (c d : ℚ) =
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (S.core.parameters.ht N) (C.block d).set : ℚ) * a d := by
    simpa [chainScale] using hcEq
  intro d r hr hNr
  have hmod : ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
      (S.core.parameters.M N : ℤ) := hdiv m C a ha c hcRel d
  have hcdvdM : c d ∣ (S.core.parameters.M N : ℤ) := by
    apply dvd_trans ?_ hmod
    refine ⟨(primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ), ?_⟩
    push_cast
    ring
  have hsmooth : OAI.RoughScales.Smooth (N + 1) (c d) := by
    intro p hp hpc
    exact S.core.parameters.Msmooth N p hp (dvd_trans hpc hcdvdM)
  have hrough : OAI.RoughScales.Rough (N + 1) (r : ℤ) := by
    intro p hp hpw hpr
    have hprNat : p ∣ r := Int.natCast_dvd.mp hpr
    have hEq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hprNat
    omega
  have hsmoothAbs : OAI.RoughScales.Smooth (N + 1) ((c d).natAbs : ℤ) := by
    have hcast : ((c d).natAbs : ℤ) = c d :=
      Int.natAbs_of_nonneg (by exact_mod_cast (hcPos d).le)
    simpa [hcast] using hsmooth
  have hcoprime := OAI.RoughProductRemoval.smooth_nat_coprime_rough hsmoothAbs hrough
  have hnum : (chainScale S.core.parameters C a N d).num = c d := by
    change ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (S.core.parameters.ht N) (C.block d).set : ℚ) * a d).num = c d
    rw [← hcEq d]
    simp
  simpa [hnum] using hcoprime

theorem chainScale_pos_eventually {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ d, 0 < chainScale S.core.parameters C a N d := by
  filter_upwards [S.core.chain_coefficients] with N hcoeff
  obtain ⟨c, hcEq, hcPos, _⟩ := hcoeff m C a ha
  intro d
  change 0 < (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
    (S.core.parameters.ht N) (C.block d).set : ℚ) * a d
  rw [← hcEq d]
  exact_mod_cast hcPos d

theorem chainScale_den_one_eventually {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ d, (chainScale S.core.parameters C a N d).den = 1 := by
  filter_upwards [S.core.chain_coefficients] with N hcoeff
  obtain ⟨c, hcEq, hcPos, _⟩ := hcoeff m C a ha
  intro d
  have hscale : chainScale S.core.parameters C a N d = (c d : ℚ) :=
    (hcEq d).symm
  rw [hscale]
  exact Rat.den_intCast _

theorem chainScale_ratio_num_coprime_eventually {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ (J : Finset (Fin m)) (hJ : J.Nonempty) k, k ∈ J → ∀ r, r.Prime →
      N + 1 < r →
      Nat.Coprime
        (chainScale S.core.parameters C a N k /
          chainScale S.core.parameters C a N (J.max' hJ)).num.natAbs r := by
  filter_upwards [chainScale_ratio_den_one_eventually S C a ha,
      chainScale_den_one_eventually S C a ha,
      chainScale_pos_eventually S C a ha,
      chainScale_num_coprime_of_prime_gt_eventually S C a ha]
    with N hratio hden hpos hunit
  intro J hJ k hk r hr hNr
  let d := J.max' hJ
  let x := chainScale S.core.parameters C a N k
  let y := chainScale S.core.parameters C a N d
  let t := x / y
  have htden : t.den = 1 := by simpa [t, x, y, d] using hratio J hJ k hk
  have hxden : x.den = 1 := hden k
  have hyden : y.den = 1 := hden d
  have htNum : (t.num : ℚ) = t := (Rat.den_eq_one_iff _).mp htden
  have hyNum : (y.num : ℚ) = y := (Rat.den_eq_one_iff _).mp hyden
  have hxNum : (x.num : ℚ) = x := (Rat.den_eq_one_iff _).mp hxden
  have hprod : t.num * y.num = x.num := by
    have hcast : ((t.num * y.num : ℤ) : ℚ) = x := by
      calc
        ((t.num * y.num : ℤ) : ℚ) = (t.num : ℚ) * (y.num : ℚ) := by norm_cast
        _ = t * y := by rw [htNum, hyNum]
        _ = x := by
          dsimp [t]
          exact div_mul_cancel₀ x (ne_of_gt (hpos d))
    have hcast' : ((t.num * y.num : ℤ) : ℚ) = (x.num : ℚ) :=
      hcast.trans hxNum.symm
    exact_mod_cast hcast'
  have hnot : ¬ r ∣ t.num.natAbs := by
    intro hdiv
    have hdivInt : (r : ℤ) ∣ t.num := Int.natCast_dvd.mpr hdiv
    have hkdivInt : (r : ℤ) ∣ x.num := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left hdivInt _
    have hkdivNat : r ∣ x.num.natAbs := Int.natCast_dvd.mp hkdivInt
    have hxcoprime : Nat.Coprime x.num.natAbs r := hunit k r hr hNr
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hxcoprime.symm hkdivNat
  have hcop : Nat.Coprime r t.num.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hr).2 hnot
  simpa [t, x, y, d] using hcop.symm

theorem rational_scale_num_cross_eq {m : ℕ} (c : Fin m → ℚ)
    (a b j k : Fin m) (ha : c a ≠ 0) (hb : c b ≠ 0)
    (haj : (c j / c a).den = 1) (hbk : (c k / c b).den = 1)
    (hak : (c k / c a).den = 1) (hbj : (c j / c b).den = 1) :
    (c j / c a).num * (c k / c b).num =
      (c k / c a).num * (c j / c b).num := by
  have hrat : c j / c a * (c k / c b) = c k / c a * (c j / c b) := by
    field_simp [ha, hb]
  have hnumA : ((c j / c a).num : ℚ) = c j / c a :=
    (Rat.den_eq_one_iff _).mp haj
  have hnumB : ((c k / c b).num : ℚ) = c k / c b :=
    (Rat.den_eq_one_iff _).mp hbk
  have hnumC : ((c k / c a).num : ℚ) = c k / c a :=
    (Rat.den_eq_one_iff _).mp hak
  have hnumD : ((c j / c b).num : ℚ) = c j / c b :=
    (Rat.den_eq_one_iff _).mp hbj
  have hcast :
      (((c j / c a).num * (c k / c b).num : ℤ) : ℚ) =
        (((c k / c a).num * (c j / c b).num : ℤ) : ℚ) := by
    calc
      _ = ((c j / c a).num : ℚ) * ((c k / c b).num : ℚ) := by simp
      _ = (c j / c a) * (c k / c b) := by rw [hnumA, hnumB]
      _ = (c k / c a) * (c j / c b) := hrat
      _ = ((c k / c a).num : ℚ) * ((c j / c b).num : ℚ) := by
        rw [hnumC, hnumD]
      _ = _ := by simp
  exact_mod_cast hcast

theorem intCast_ne_zero_of_natAbs_coprime {r : ℕ} (hr : r.Prime) (z : ℤ)
    (hz : Nat.Coprime z.natAbs r) : (z : ZMod r) ≠ 0 := by
  intro hzero
  have hdiv : (r : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z r).mp hzero
  have hdivNat : r ∣ z.natAbs := Int.natCast_dvd.mp hdiv
  exact (Nat.Prime.coprime_iff_not_dvd hr).mp hz.symm hdivNat

theorem rowShapeScaleNumerator_unit_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r) :
    ∀ᶠ N in atTop, ∀ R k, k ∈ (Sh.row R).support → ∀ v, v.Prime →
      N + 1 < v →
      ((chainScale S.core.parameters C a N k /
        chainScale S.core.parameters C a N (Sh.row R).anchor).num : ZMod v) ≠ 0 := by
  filter_upwards [chainScale_ratio_num_coprime_eventually S C a ha] with N hunit
  intro R k hk v hv hNv
  apply intCast_ne_zero_of_natAbs_coprime hv
  exact hunit (Sh.row R).support (Sh.row R).support_nonempty k hk v hv hNv

theorem pool_lower_gt_masterScaleV_eventually {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop, masterScaleV S.core.parameters N l <
      (S.primeStage.pool N l).lower := by
  have hdom := S.primeStage.pool_lower_dominates l 1 (by norm_num)
  have hlarge : ∀ᶠ N in atTop,
      1 < (S.primeStage.pool N l).lower / (masterScaleV S.core.parameters N l : ℝ) := by
    simpa [Real.rpow_one] using hdom.eventually_gt_atTop 1
  filter_upwards [hlarge] with N hN
  have hV : 0 < (masterScaleV S.core.parameters N l : ℝ) := by
    unfold masterScaleV
    positivity
  have hlt' := (lt_div_iff₀ hV).mp hN
  have hlt : (masterScaleV S.core.parameters N l : ℝ) <
      ((S.primeStage.pool N l).lower : ℝ) := by simpa using hlt'
  exact_mod_cast hlt

def RowTemplate.valueNat {m q : ℕ} (T : RowTemplate m q) (p : Fin q → ℕ)
    (k : Fin m) : ℕ := (T.entry k).elim 0 fun e => ∏ i, p i ^ e i

theorem RowTemplate.value_eq_valueNat {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (k : Fin m) : T.value p k = (T.valueNat p k : ℚ) := by
  cases h : T.entry k <;> simp [RowTemplate.value, RowTemplate.valueNat, h]

def rowTemplateIntegerCoefficient {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (p : Fin q → ℕ) (k : Fin m) : ℤ :=
  (c k / c T.anchor).num * (T.valueNat p k : ℤ)

theorem RowTemplate.mem_support_of_valueNat_ne_zero {m q : ℕ}
    (T : RowTemplate m q) (p : Fin q → ℕ) (k : Fin m)
    (hval : T.valueNat p k ≠ 0) : k ∈ T.support := by
  cases h : T.entry k with
  | none => simp [RowTemplate.valueNat, RowTemplate.support, h] at hval
  | some e => simp [RowTemplate.support, h]

theorem rowTemplateIntegerMinor_factor {m q : ℕ} (c : Fin m → ℚ)
    (T U : RowTemplate m q) (p : Fin q → ℕ) (r : ℕ) (hr : r.Prime)
    (hTa : c T.anchor ≠ 0) (hUa : c U.anchor ≠ 0)
    (hdenT : ∀ i, i ∈ T.support → (c i / c T.anchor).den = 1)
    (hdenU : ∀ i, i ∈ U.support → (c i / c U.anchor).den = 1)
    (hunitT : ∀ i, i ∈ T.support →
      ((c i / c T.anchor).num : ZMod r) ≠ 0)
    (hunitU : ∀ i, i ∈ U.support →
      ((c i / c U.anchor).num : ZMod r) ≠ 0)
    (j k : Fin m) :
    ∃ F : ℤ,
      rowTemplateIntegerCoefficient c T p j *
          rowTemplateIntegerCoefficient c U p k -
        rowTemplateIntegerCoefficient c T p k *
          rowTemplateIntegerCoefficient c U p j =
        F * (((T.valueNat p j * U.valueNat p k : ℕ) : ℤ) -
          ((T.valueNat p k * U.valueNat p j : ℕ) : ℤ)) ∧
      (F : ZMod r) ≠ 0 := by
  let v₁ := T.valueNat p j
  let v₂ := U.valueNat p k
  let v₃ := T.valueNat p k
  let v₄ := U.valueNat p j
  let n₁ := (c j / c T.anchor).num
  let n₂ := (c k / c U.anchor).num
  let n₃ := (c k / c T.anchor).num
  let n₄ := (c j / c U.anchor).num
  letI : Fact r.Prime := ⟨hr⟩
  have hdet :
      rowTemplateIntegerCoefficient c T p j *
          rowTemplateIntegerCoefficient c U p k -
        rowTemplateIntegerCoefficient c T p k *
          rowTemplateIntegerCoefficient c U p j =
        n₁ * n₂ * ((v₁ : ℤ) * (v₂ : ℤ)) -
          n₃ * n₄ * ((v₃ : ℤ) * (v₄ : ℤ)) := by
    simp [rowTemplateIntegerCoefficient, n₁, n₂, n₃, n₄, v₁, v₂, v₃, v₄]
    ring
  have hcast₁ : ((v₁ * v₂ : ℕ) : ℤ) = (v₁ : ℤ) * (v₂ : ℤ) := by
    norm_cast
  have hcast₂ : ((v₃ * v₄ : ℕ) : ℤ) = (v₃ : ℤ) * (v₄ : ℤ) := by
    norm_cast
  have support_of_ne {V : RowTemplate m q} (i : Fin m)
      (hval : V.valueNat p i ≠ 0) : i ∈ V.support :=
    V.mem_support_of_valueNat_ne_zero p i hval
  by_cases hfirst : v₁ * v₂ ≠ 0
  · have hv₁ : v₁ ≠ 0 := by
      intro hz
      apply hfirst
      simp [hz]
    have hv₂ : v₂ ≠ 0 := by
      intro hz
      apply hfirst
      simp [hz]
    have hjT := support_of_ne (V := T) j hv₁
    have hkU := support_of_ne (V := U) k hv₂
    have hFunit : ((n₁ * n₂ : ℤ) : ZMod r) ≠ 0 := by
      simpa [n₁, n₂] using mul_ne_zero (hunitT j hjT) (hunitU k hkU)
    by_cases hsecond : v₃ * v₄ ≠ 0
    · have hv₃ : v₃ ≠ 0 := by
        intro hz
        apply hsecond
        simp [hz]
      have hv₄ : v₄ ≠ 0 := by
        intro hz
        apply hsecond
        simp [hz]
      have hkT := support_of_ne (V := T) k hv₃
      have hjU := support_of_ne (V := U) j hv₄
      have hcross := rational_scale_num_cross_eq c T.anchor U.anchor j k hTa hUa
        (hdenT j hjT) (hdenU k hkU) (hdenT k hkT) (hdenU j hjU)
      refine ⟨n₁ * n₂, ?_, hFunit⟩
      rw [hdet, ← hcast₁, ← hcast₂, ← hcross]
      ring
    · have hzero₂ : ((v₃ * v₄ : ℕ) : ℤ) = 0 := by
        have hn : v₃ * v₄ = 0 := by
          by_contra hne
          exact hsecond hne
        exact_mod_cast hn
      refine ⟨n₁ * n₂, ?_, hFunit⟩
      rw [hdet, ← hcast₁, ← hcast₂, hzero₂]
      ring
  · by_cases hsecond : v₃ * v₄ ≠ 0
    · have hv₃ : v₃ ≠ 0 := by
        intro hz
        apply hsecond
        simp [hz]
      have hv₄ : v₄ ≠ 0 := by
        intro hz
        apply hsecond
        simp [hz]
      have hkT := support_of_ne (V := T) k hv₃
      have hjU := support_of_ne (V := U) j hv₄
      have hFunit : ((n₃ * n₄ : ℤ) : ZMod r) ≠ 0 := by
        simpa [n₃, n₄] using mul_ne_zero (hunitT k hkT) (hunitU j hjU)
      have hzero₁ : ((v₁ * v₂ : ℕ) : ℤ) = 0 := by
        have hn : v₁ * v₂ = 0 := by
          by_contra hne
          exact hfirst hne
        exact_mod_cast hn
      refine ⟨n₃ * n₄, ?_, hFunit⟩
      rw [hdet, ← hcast₁, ← hcast₂, hzero₁]
      ring
    · have hzero₁ : ((v₁ * v₂ : ℕ) : ℤ) = 0 := by
        have hn : v₁ * v₂ = 0 := by
          by_contra hne
          exact hfirst hne
        exact_mod_cast hn
      have hzero₂ : ((v₃ * v₄ : ℕ) : ℤ) = 0 := by
        have hn : v₃ * v₄ = 0 := by
          by_contra hne
          exact hsecond hne
        exact_mod_cast hn
      refine ⟨1, ?_, by norm_num⟩
      rw [hdet, ← hcast₁, ← hcast₂, hzero₁, hzero₂]
      simp

def rowShapeLinearCoefficientsInt {m q r s : ℕ} (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (c : Fin m → ℚ) :
    ℕ → (Fin s → ℕ) → Fin r → Fin m → ℤ :=
  fun _ p R k => (c k / c (Sh.row R).anchor).num *
    ((Sh.row R).valueNat (fun i => p (ι i)) k : ℤ)

theorem rowShapeLinearCoefficients_eq_intCast_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) :
    ∀ᶠ N in atTop, ∀ p R k,
      rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N) N p R k =
        (rowShapeLinearCoefficientsInt Sh ι
          (chainScale S.core.parameters C a N) N p R k : ℚ) := by
  filter_upwards [chainScale_ratio_den_one_eventually S C a ha] with N hratio
  intro p R k
  let T := Sh.row R
  let c := chainScale S.core.parameters C a N
  by_cases hk : k ∈ T.support
  · have hden : (c k / c T.anchor).den = 1 :=
      hratio T.support T.support_nonempty k hk
    have hnum : ((c k / c T.anchor).num : ℚ) = c k / c T.anchor :=
      (Rat.den_eq_one_iff _).mp hden
    change (c k / c T.anchor) * T.value (fun i => p (ι i)) k =
      (((c k / c T.anchor).num *
        (T.valueNat (fun i => p (ι i)) k : ℤ) : ℤ) : ℚ)
    calc
      (c k / c T.anchor) * T.value (fun i => p (ι i)) k =
          ((c k / c T.anchor).num : ℚ) *
            (T.valueNat (fun i => p (ι i)) k : ℚ) := by
              conv_lhs => rw [← hnum, T.value_eq_valueNat]
      _ = (((c k / c T.anchor).num *
            (T.valueNat (fun i => p (ι i)) k : ℤ) : ℤ) : ℚ) := by
              rw [Int.cast_mul, Int.cast_natCast]
  · have hnone : T.entry k = none := by
      cases h : T.entry k with
      | none => rfl
      | some e => exact (hk (by simp [RowTemplate.support, h])).elim
    simp [rowShapeLinearCoefficients, rowShapeLinearCoefficientsInt,
      RowTemplate.value, RowTemplate.valueNat, T, c, hnone]

theorem RowTemplate.valueNat_cast_ne_zero_of_slot_not_dvd {m q : ℕ}
    (T : RowTemplate m q) (p : Fin q → ℕ) (k : Fin m) (r : ℕ)
    (hr : r.Prime) (hk : k ∈ T.support) (hslot : ∀ i, ¬ r ∣ p i) :
    ((T.valueNat p k : ℕ) : ZMod r) ≠ 0 := by
  letI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e, he⟩ := T.entry_exists_of_mem_support k hk
  have hv : T.valueNat p k = ∏ i, p i ^ e i := by
    simp [RowTemplate.valueNat, he]
  rw [hv]
  simp only [Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  intro hz
  exact hslot i ((ZMod.natCast_eq_zero_iff (p i) r).mp hz)

theorem RowTemplate.value_eq_monomial_scale_of_parallel {m q : ℕ}
    (T T' : RowTemplate m q) (hpar : T.Parallel T') (p : Fin q → ℕ)
    (hp : ∀ i, p i ≠ 0) :
    ∀ k,
      T'.value p k =
        (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * T.value p k := by
  let δ := Classical.choose hpar.2
  have hδ := Classical.choose_spec hpar.2
  have hsupport := hpar.1
  intro k
  cases hT : T.entry k with
  | none =>
      have hT' : T'.entry k = none := by
        by_contra hsome
        cases h : T'.entry k with
        | none => exact hsome h
        | some e' =>
            have hk : k ∈ T'.support := by simp [RowTemplate.support, h]
            have : k ∈ T.support := by simpa [hsupport] using hk
            simp [RowTemplate.support, hT] at this
      simp [RowTemplate.value, hT, hT']
  | some e =>
      have hk : k ∈ T.support := by simp [RowTemplate.support, hT]
      have hk' : k ∈ T'.support := by simpa [hsupport] using hk
      obtain ⟨e', he'⟩ := T'.entry_exists_of_mem_support k hk'
      have hfactor (i : Fin q) :
          (p i : ℚ) ^ e' i = (p i : ℚ) ^ e i * (p i : ℚ) ^ δ i := by
        have hpq : (p i : ℚ) ≠ 0 := by exact_mod_cast hp i
        have hExp := hδ k e e' hT he' i
        rw [← zpow_natCast, ← zpow_natCast]
        rw [hExp, zpow_add₀ hpq]
      simp only [RowTemplate.value, hT, he']
      change (∏ i, (p i : ℚ) ^ e' i) =
        (∏ i, (p i : ℚ) ^ δ i) * ∏ i, (p i : ℚ) ^ e i
      calc
        (∏ i, (p i : ℚ) ^ e' i) =
            ∏ i, ((p i : ℚ) ^ e i * (p i : ℚ) ^ δ i) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hfactor i
        _ = (∏ i, (p i : ℚ) ^ e i) * ∏ i, (p i : ℚ) ^ δ i :=
              Finset.prod_mul_distrib
        _ = (∏ i, (p i : ℚ) ^ δ i) * ∏ i, (p i : ℚ) ^ e i := by ring

theorem RowTemplate.value_ne_zero_of_slots {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (k : Fin m) (hk : k ∈ T.support)
    (hp : ∀ i, p i ≠ 0) : T.value p k ≠ 0 := by
  obtain ⟨e, he⟩ := T.entry_exists_of_mem_support k hk
  rw [RowTemplate.value, he]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  exact_mod_cast hp i

theorem rowForm_basis_anchor_eq_value {m q : ℕ}
    (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (hc : c T.anchor ≠ 0) :
    rowForm c T p (fun k => if k = T.anchor then 1 else 0) = T.value p T.anchor := by
  unfold rowForm
  rw [Finset.sum_eq_single T.anchor]
  · simp [div_self hc]
  · intro k hk hka
    simp [hka]
  · intro h
    exact (h (Finset.mem_univ T.anchor)).elim

theorem RowTemplate.rowForm_eq_monomial_scale_of_parallel {m q : ℕ}
    (c : Fin m → ℚ) (T T' : RowTemplate m q) (hpar : T.Parallel T')
    (p : Fin q → ℕ) (hp : ∀ i, p i ≠ 0) :
    ∀ z : Fin m → ℚ,
      rowForm c T' p z =
        (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * rowForm c T p z := by
  have hvalue := T.value_eq_monomial_scale_of_parallel T' hpar p hp
  have hanchor : T'.anchor = T.anchor := by
    apply le_antisymm
    · apply Finset.max'_le
      intro k hk
      have hk' : k ∈ T.support := by simpa [hpar.1] using hk
      exact Finset.le_max' T.support k hk'
    · apply Finset.max'_le
      intro k hk
      have hk' : k ∈ T'.support := by simpa [hpar.1] using hk
      exact Finset.le_max' T'.support k hk'
  intro z
  let scale : ℚ := ∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)
  unfold rowForm
  rw [hanchor]
  calc
    (∑ k, c k / c T.anchor * T'.value p k * z k) =
        ∑ k, scale * (c k / c T.anchor * T.value p k * z k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hvalue k]
          simp only [scale]
          ring
    _ = scale * ∑ k, c k / c T.anchor * T.value p k * z k := by
          rw [Finset.mul_sum]

def dropPrimeTuple2 {q : ℕ} (p : Fin (q + 2) → ℕ) : Fin q → ℕ :=
  fun i => p i.succ.succ

theorem RowTemplate.anchor_eq_of_support_eq {m q q' : ℕ}
    (T : RowTemplate m q) (U : RowTemplate m q')
    (h : T.support = U.support) : T.anchor = U.anchor := by
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    have hk' : k ∈ U.support := by simpa [h] using hk
    exact Finset.le_max' U.support k hk'
  · apply Finset.max'_le
    intro k hk
    have hk' : k ∈ T.support := by simpa [h] using hk
    exact Finset.le_max' T.support k hk'

def outsideBranchMaskFunction {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u : Fin m) (U : Finset (Fin m))
    (p : Fin (q + 2) → ℕ) (y : ℤ) : ℝ :=
  f U (dropPrimeTuple2 p)
      ((if u ∈ U then (p 1 : ℤ) else 1) * y) *
    f U (dropPrimeTuple2 p)
      ((if u ∈ U then (p 0 : ℤ) else 1) * y)

def balancedBranchMaskFunction {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u v : Fin m) (U : Finset (Fin m))
    (p : Fin (q + 2) → ℕ) (y : ℤ) : ℝ :=
  f U (dropPrimeTuple2 p)
      ((if u ∈ U then (p 0 : ℤ) else 1) *
        (if v ∈ U then (p 1 : ℤ) else 1) * y) *
    f U (dropPrimeTuple2 p)
      ((if v ∈ U then (p 0 : ℤ) else 1) *
        (if u ∈ U then (p 1 : ℤ) else 1) * y)

theorem pkgMask_outsideBranchMask_substitution {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u : Fin m) (U : Finset (Fin m)) (p : Fin (q + 2) → ℕ)
    (z : Fin m → ℤ) :
    outsideBranchMaskFunction f u U p (∏ k ∈ U, z k) =
      f U (dropPrimeTuple2 p)
          (∏ k ∈ U, Function.update z u ((p 1 : ℤ) * z u) k) *
        f U (dropPrimeTuple2 p)
          (∏ k ∈ U, Function.update z u ((p 0 : ℤ) * z u) k) := by
  unfold outsideBranchMaskFunction
  rw [← mask_product_scale_at U u z (p 1 : ℤ),
    ← mask_product_scale_at U u z (p 0 : ℤ)]

theorem pkgMask_balancedBranchMask_substitution {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u v : Fin m) (U : Finset (Fin m)) (huv : u ≠ v)
    (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) :
    balancedBranchMaskFunction f u v U p (∏ k ∈ U, z k) =
      f U (dropPrimeTuple2 p)
          (∏ k ∈ U, Function.update (Function.update z u
            ((p 0 : ℤ) * z u)) v
            ((p 1 : ℤ) * Function.update z u ((p 0 : ℤ) * z u) v) k) *
        f U (dropPrimeTuple2 p)
          (∏ k ∈ U, Function.update (Function.update z v
            ((p 0 : ℤ) * z v)) u
            ((p 1 : ℤ) * Function.update z v ((p 0 : ℤ) * z v) u) k) := by
  unfold balancedBranchMaskFunction
  rw [← mask_product_scale_two U u v huv z (p 0 : ℤ) (p 1 : ℤ),
    ← mask_product_scale_two U v u (Ne.symm huv) z (p 0 : ℤ) (p 1 : ℤ)]

theorem outsideBranchMaskFunction_abs_le {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u : Fin m) (U : Finset (Fin m)) (p : Fin (q + 2) → ℕ) (y : ℤ)
    (hf : ∀ U p y, |f U p y| ≤ 1) :
    |outsideBranchMaskFunction f u U p y| ≤ 1 := by
  unfold outsideBranchMaskFunction
  rw [abs_mul]
  calc
    |f U (dropPrimeTuple2 p) ((if u ∈ U then (p 1 : ℤ) else 1) * y)| *
        |f U (dropPrimeTuple2 p) ((if u ∈ U then (p 0 : ℤ) else 1) * y)| ≤ 1 * 1 := by
          exact mul_le_mul (hf U _ _) (hf U _ _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem balancedBranchMaskFunction_abs_le {m q : ℕ}
    (f : Finset (Fin m) → (Fin q → ℕ) → ℤ → ℝ)
    (u v : Fin m) (U : Finset (Fin m)) (p : Fin (q + 2) → ℕ) (y : ℤ)
    (hf : ∀ U p y, |f U p y| ≤ 1) :
    |balancedBranchMaskFunction f u v U p y| ≤ 1 := by
  unfold balancedBranchMaskFunction
  rw [abs_mul]
  calc
    |f U (dropPrimeTuple2 p)
          ((if u ∈ U then (p 0 : ℤ) else 1) * (if v ∈ U then (p 1 : ℤ) else 1) * y)| *
        |f U (dropPrimeTuple2 p)
          ((if v ∈ U then (p 0 : ℤ) else 1) * (if u ∈ U then (p 1 : ℤ) else 1) * y)| ≤ 1 * 1 := by
          exact mul_le_mul (hf U _ _) (hf U _ _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem extendPrimeTuple2_drop {q : ℕ} (p : Fin (q + 2) → ℕ) :
    extendPrimeTuple (extendPrimeTuple (dropPrimeTuple2 p) (p 1)) (p 0) = p := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [extendPrimeTuple]
  · intro i
    refine Fin.cases ?_ ?_ i
    · change (extendPrimeTuple (dropPrimeTuple2 p) (p 1)) 0 = p 1
      rfl
    · intro j
      change (dropPrimeTuple2 p j) = p (j.succ.succ)
      rfl

theorem dropPrimeTuple2_extend {q : ℕ} (p : Fin q → ℕ) (p₁ p₀ : ℕ) :
    dropPrimeTuple2 (extendPrimeTuple (extendPrimeTuple p p₁) p₀) = p := by
  funext i
  simp [dropPrimeTuple2, extendPrimeTuple]

theorem pkgMask_gapSlotMass_extend2 {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (p : Fin q → ℕ) (p₁ p₀ : ℕ) :
    gapSlotMass S C.gap N (extendPrimeTuple (extendPrimeTuple p p₁) p₀) =
      gapSlotMass S C.gap N p *
        primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper p₁ *
        primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper p₀ := by
  unfold gapSlotMass independentPrimePoolMass
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hslot₁ :
      (extendPrimeTuple (extendPrimeTuple p p₁) p₀)
        (Fin.succ (0 : Fin (q + 1))) = p₁ := by
    change (extendPrimeTuple p p₁) 0 = p₁
    rfl
  rw [hslot₁]
  simp [extendPrimeTuple]
  ring

theorem rowForm_scaleBranchP_tuple2 {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (u : Fin m) (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBranchP u) p (fun k => (z k : ℚ)) =
      rowForm c T (dropPrimeTuple2 p)
        (Function.update (fun k => (z k : ℚ)) u
          ((p 1 : ℚ) * (z u : ℚ))) := by
  rw [← extendPrimeTuple2_drop p]
  exact rowForm_scaleBranchP c T u (dropPrimeTuple2 p) (p 1) (p 0) z

theorem rowForm_scaleBranchQ_tuple2 {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (u : Fin m) (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBranchQ u) p (fun k => (z k : ℚ)) =
      rowForm c T (dropPrimeTuple2 p)
        (Function.update (fun k => (z k : ℚ)) u
          ((p 0 : ℚ) * (z u : ℚ))) := by
  rw [← extendPrimeTuple2_drop p]
  exact rowForm_scaleBranchQ c T u (dropPrimeTuple2 p) (p 1) (p 0) z

theorem rowForm_scaleBalancedP_tuple2 {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (u v : Fin m) (huv : u ≠ v)
    (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBalancedP u v) p (fun k => (z k : ℚ)) =
      rowForm c T (dropPrimeTuple2 p)
        (Function.update (Function.update (fun k => (z k : ℚ)) u
          ((p 0 : ℚ) * (z u : ℚ))) v ((p 1 : ℚ) * (z v : ℚ))) := by
  rw [← extendPrimeTuple2_drop p]
  exact rowForm_scaleBalancedP c T u v huv (dropPrimeTuple2 p) (p 1) (p 0) z

theorem rowForm_scaleBalancedQ_tuple2 {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (u v : Fin m) (huv : u ≠ v)
    (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) :
    rowForm c (T.scaleBalancedQ u v) p (fun k => (z k : ℚ)) =
      rowForm c T (dropPrimeTuple2 p)
        (Function.update (Function.update (fun k => (z k : ℚ)) v
          ((p 0 : ℚ) * (z v : ℚ))) u ((p 1 : ℚ) * (z u : ℚ))) := by
  rw [← extendPrimeTuple2_drop p]
  exact rowForm_scaleBalancedQ c T u v huv (dropPrimeTuple2 p) (p 1) (p 0) z

noncomputable def combineParallelRowFunction {q : ℕ}
    (f : (Fin q → ℕ) → ℤ → ℝ) (scale : (Fin (q + 2) → ℕ) → ℚ)
    (W : ℤ → ℝ) (p : Fin (q + 2) → ℕ) (y : ℤ) : ℝ :=
  f (dropPrimeTuple2 p) y *
    atQ (f (dropPrimeTuple2 p)) (scale p * (y : ℚ)) / W y

noncomputable def RowTemplate.parallelScaleFactor {m q : ℕ}
    (T T' : RowTemplate m q) (hpar : T.Parallel T') (p : Fin q → ℕ) : ℚ :=
  ∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)

theorem combineParallelRowFunction_abs_le {q : ℕ}
    (f : (Fin q → ℕ) → ℤ → ℝ) (scale : (Fin (q + 2) → ℕ) → ℚ)
    (W : ℤ → ℝ) (p : Fin (q + 2) → ℕ)
    (hW : ∀ y, 0 ≤ W y) (hWpos : ∀ y, 0 < W y)
    (hf : ∀ p y, |f p y| ≤ W y)
    (hinv : ∀ y : ℤ, (scale p * (y : ℚ)).den = 1 →
      W ((scale p * (y : ℚ)).num) = W y) (y : ℤ) :
    |combineParallelRowFunction f scale W p y| ≤ W y := by
  unfold combineParallelRowFunction
  by_cases hden : (scale p * (y : ℚ)).den = 1
  · rw [atQ, if_pos hden]
    have h1 : |f (dropPrimeTuple2 p) y| ≤ W y := hf _ _
    have h2 : |f (dropPrimeTuple2 p) (scale p * (y : ℚ)).num| ≤
        W (scale p * (y : ℚ)).num := hf _ _
    rw [hinv y hden] at h2
    have hw : 0 < W y := hWpos y
    rw [abs_div, abs_mul, abs_of_nonneg (hW y)]
    calc
      (|f (dropPrimeTuple2 p) y| * |f (dropPrimeTuple2 p) (scale p * (y : ℚ)).num|) / W y ≤
          (W y * W y) / W y := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul h1 h2 (abs_nonneg _) (hW y)
            · exact hW y
      _ = W y := by field_simp [ne_of_gt hw]
  · simp [atQ, hden, hW y]

theorem rowForm_update_of_not_mem_support {m q : ℕ}
    (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (u : Fin m) (v : ℚ) (hu : u ∉ T.support) :
    rowForm c T p (Function.update z u v) = rowForm c T p z := by
  unfold rowForm
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hku : k = u
  · subst k
    have hnone : T.entry u = none := by
      cases h : T.entry u with
      | none => rfl
      | some e => exact (hu (by simp [RowTemplate.support, h])).elim
    simp [RowTemplate.value, hnone]
  · simp [Function.update_of_ne hku]

theorem rowForm_update_mul_singleton {m q : ℕ}
    (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (u : Fin m) (v : ℚ)
    (hsupport : T.support = {u}) (hc : c u ≠ 0) :
    rowForm c T p (Function.update z u (v * z u)) = v * rowForm c T p z := by
  have hanchor : T.anchor = u := by
    simp [RowTemplate.anchor, hsupport]
  have hform (z : Fin m → ℚ) : rowForm c T p z = T.value p u * z u := by
    unfold rowForm
    rw [Finset.sum_eq_single u]
    · simp [hanchor, div_self hc]
    · intro k hk hku
      have hk' : k ∉ T.support := by
        simp [hsupport, hku]
      have hnone : T.entry k = none := by
        cases h : T.entry k with
        | none => rfl
        | some e => exact (hk' (by simp [RowTemplate.support, h])).elim
      simp [RowTemplate.value, hnone]
    · intro hu
      exact (hu (Finset.mem_univ u)).elim
  rw [hform, hform]
  simp [Function.update_self]
  ring

theorem pkgMask_chainWeight_scaleBranchP_eq {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (c : Fin m → ℚ)
    (T : RowTemplate m q) (u : Fin m) (p : Fin (q + 2) → ℕ)
    (z : Fin m → ℤ)
    (hpar : (T.scaleBranchP u).Parallel (T.scaleBranchQ u))
    (hc : c u ≠ 0) (hp₁ : (p 1).Prime)
    (hV₁ : masterScaleV S.core.parameters N C.gap < p 1)
    (hdenBranch :
      (rowForm c (T.scaleBranchP u) p fun k => (z k : ℚ)).den = 1)
    (hdenOld :
      (rowForm c T (dropPrimeTuple2 p) fun k => (z k : ℚ)).den = 1) :
    chainWeight S.core.parameters C N d
        (rowForm c (T.scaleBranchP u) p (fun k => (z k : ℚ))).num =
      chainWeight S.core.parameters C N d
        (rowForm c T (dropPrimeTuple2 p) (fun k => (z k : ℚ))).num := by
  let oldp := dropPrimeTuple2 p
  let zQ : Fin m → ℚ := fun k => (z k : ℚ)
  let value := rowForm c T oldp zQ
  let branchValue := rowForm c (T.scaleBranchP u) p zQ
  have hrowUpdate := rowForm_scaleBranchP_tuple2 c T u p z
  have hbranchNum : (branchValue.num : ℚ) = branchValue :=
    (Rat.den_eq_one_iff branchValue).mp (by simpa [branchValue] using hdenBranch)
  have holdNum : (value.num : ℚ) = value :=
    (Rat.den_eq_one_iff value).mp (by simpa [value, oldp, zQ] using hdenOld)
  rcases T.scaleBranches_parallel_support u hpar with hu | hsingle
  · have hEq : branchValue = value := by
      dsimp [branchValue, value, oldp, zQ] at *
      rw [hrowUpdate]
      exact rowForm_update_of_not_mem_support c T (dropPrimeTuple2 p)
        (fun k => (z k : ℚ)) u ((p 1 : ℚ) * (z u : ℚ)) hu
    have hnumQ : (branchValue.num : ℚ) = (value.num : ℚ) := by
      calc
        (branchValue.num : ℚ) = branchValue := hbranchNum
        _ = value := hEq
        _ = (value.num : ℚ) := holdNum.symm
    have hnum : branchValue.num = value.num := by exact_mod_cast hnumQ
    rw [hnum]
  · have hEq : branchValue = (p 1 : ℚ) * value := by
      dsimp [branchValue, value, oldp, zQ] at *
      rw [hrowUpdate]
      exact rowForm_update_mul_singleton c T (dropPrimeTuple2 p)
        (fun k => (z k : ℚ)) u (p 1 : ℚ) hsingle hc
    have hnumQ : (branchValue.num : ℚ) = ((p 1 : ℤ) * value.num : ℤ) := by
      calc
        (branchValue.num : ℚ) = branchValue := hbranchNum
        _ = (p 1 : ℚ) * value := hEq
        _ = (p 1 : ℚ) * (value.num : ℚ) := by rw [holdNum]
        _ = ((p 1 : ℤ) * value.num : ℤ) := by norm_cast
    have hnum : branchValue.num = (p 1 : ℤ) * value.num := by exact_mod_cast hnumQ
    rw [hnum]
    exact chainWeight_mul_eq_of_prime_gt S C N d (p 1) hp₁ hV₁ value.num

theorem pkgMask_invariantBranchWeightProduct_eq_old {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (a : Fin m → ℚ) (T : Fin r → RowTemplate m q) (u : Fin m)
    (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ) (I : Fin r → Prop)
    (hI : ∀ i, I i ↔ ((T i).scaleBranchP u).Parallel ((T i).scaleBranchQ u))
    (hc : chainScale S.core.parameters C a N u ≠ 0) (hp₁ : (p 1).Prime)
    (hV₁ : masterScaleV S.core.parameters N C.gap < p 1)
    (hdenBranch : ∀ i,
      (rowForm (chainScale S.core.parameters C a N) ((T i).scaleBranchP u) p
        fun k => (z k : ℚ)).den = 1)
    (hdenOld : ∀ i,
      (rowForm (chainScale S.core.parameters C a N) (T i) (dropPrimeTuple2 p)
        fun k => (z k : ℚ)).den = 1) :
    (∏ i : Fin r, if hi : I i then
        1 + chainWeight S.core.parameters C N (T i).anchor
          (rowForm (chainScale S.core.parameters C a N) ((T i).scaleBranchP u) p
            fun k => (z k : ℚ)).num else 1) =
      ∏ i : Fin r, if hi : I i then
        1 + chainWeight S.core.parameters C N (T i).anchor
          (rowForm (chainScale S.core.parameters C a N) (T i) (dropPrimeTuple2 p)
            fun k => (z k : ℚ)).num else 1 := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hinv : I i
  ·
    have hwt := pkgMask_chainWeight_scaleBranchP_eq S C N (T i).anchor
      (chainScale S.core.parameters C a N) (T i) u p z
      ((hI i).mp hinv) hc hp₁ hV₁ (hdenBranch i) (hdenOld i)
    rw [hwt]
  · simp [hinv]

theorem RowTemplate.scaleBranch_parallel_factor_eq {m q : ℕ}
    (T : RowTemplate m q) (u : Fin m) (p : Fin (q + 2) → ℕ)
    (hp : ∀ i, p i ≠ 0)
    (hpar : (T.scaleBranchP u).Parallel (T.scaleBranchQ u)) :
    (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) =
      if T.support = {u} then (p 0 : ℚ) / (p 1 : ℚ) else 1 := by
  classical
  let c : Fin m → ℚ := fun _ => 1
  let oldp := dropPrimeTuple2 p
  let z₀ : Fin m → ℤ := fun k => if k = T.anchor then 1 else 0
  let z₀Q : Fin m → ℚ := fun k => (z₀ k : ℚ)
  have hpOld : ∀ i, oldp i ≠ 0 := fun i => hp i.succ.succ
  have hOldEq : rowForm c T oldp z₀Q = T.value oldp T.anchor := by
    simpa [c, z₀, z₀Q] using rowForm_basis_anchor_eq_value c T oldp (by norm_num)
  have hOldNe : rowForm c T oldp z₀Q ≠ 0 := by
    rw [hOldEq]
    exact T.value_ne_zero_of_slots oldp T.anchor
      (Finset.max'_mem T.support T.support_nonempty) hpOld
  have hscale := RowTemplate.rowForm_eq_monomial_scale_of_parallel
    c (T.scaleBranchP u) (T.scaleBranchQ u) hpar p hp z₀Q
  rcases T.scaleBranches_parallel_support u hpar with hu | hsingle
  · have hP : rowForm c (T.scaleBranchP u) p z₀Q = rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBranchP_tuple2]
      exact rowForm_update_of_not_mem_support c T oldp z₀Q u
        ((p 1 : ℚ) * z₀Q u) hu
    have hQ : rowForm c (T.scaleBranchQ u) p z₀Q = rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBranchQ_tuple2]
      exact rowForm_update_of_not_mem_support c T oldp z₀Q u
        ((p 0 : ℚ) * z₀Q u) hu
    have hfactor : (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) = 1 := by
      have hEq : rowForm c T oldp z₀Q =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * rowForm c T oldp z₀Q := by
        simpa [hP, hQ] using hscale
      have hcancel :
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * rowForm c T oldp z₀Q =
            1 * rowForm c T oldp z₀Q := by simpa using hEq.symm
      exact mul_right_cancel₀ hOldNe hcancel
    have hnotSingle : T.support ≠ {u} := by
      intro h
      apply hu
      rw [h]
      simp
    simp [hnotSingle, hfactor]
  · have hP : rowForm c (T.scaleBranchP u) p z₀Q =
        (p 1 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBranchP_tuple2]
      change rowForm c T oldp
        (Function.update z₀Q u ((p 1 : ℚ) * z₀Q u)) = _
      exact rowForm_update_mul_singleton c T oldp z₀Q u (p 1 : ℚ)
        hsingle (by norm_num [c])
    have hQ : rowForm c (T.scaleBranchQ u) p z₀Q =
        (p 0 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBranchQ_tuple2]
      change rowForm c T oldp
        (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)) = _
      exact rowForm_update_mul_singleton c T oldp z₀Q u (p 0 : ℚ)
        hsingle (by norm_num [c])
    have hp1 : (p 1 : ℚ) ≠ 0 := by exact_mod_cast hp 1
    have hfactor : (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) =
        (p 0 : ℚ) / (p 1 : ℚ) := by
      have hEq : (p 0 : ℚ) * rowForm c T oldp z₀Q =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) *
            ((p 1 : ℚ) * rowForm c T oldp z₀Q) := by
        simpa [hP, hQ, mul_assoc] using hscale
      have hcancel : (p 0 : ℚ) =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (p 1 : ℚ) :=
        mul_right_cancel₀ hOldNe (by simpa [mul_assoc] using hEq)
      field_simp [hp1]
      nlinarith [hcancel]
    simp [hsingle, hfactor]

theorem chainWeight_scaleBranch_invariant {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) {q : ℕ}
    (T : RowTemplate m q) (u : Fin m) (p : Fin (q + 2) → ℕ)
    (hp : ∀ i, p i ≠ 0) (hp₀ : (p 0).Prime) (hp₁ : (p 1).Prime)
    (hV₀ : masterScaleV S.core.parameters N C.gap < p 0)
    (hV₁ : masterScaleV S.core.parameters N C.gap < p 1)
    (hne : p 0 ≠ p 1) (hpar : (T.scaleBranchP u).Parallel (T.scaleBranchQ u))
    (y : ℤ)
    (hden : ((∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (y : ℚ)).den = 1) :
    chainWeight S.core.parameters C N d
      (((∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (y : ℚ)).num) =
        chainWeight S.core.parameters C N d y := by
  have hfactor := T.scaleBranch_parallel_factor_eq u p hp hpar
  rw [hfactor] at hden ⊢
  by_cases hs : T.support = {u}
  · simp only [if_pos hs] at hden ⊢
    exact chainWeight_rat_div_mul_eq_of_prime_gt S C N d (p 0) (p 1)
      hp₀ hp₁ hV₀ hV₁ hne y hden
  · simp only [if_neg hs] at hden ⊢
    simp

theorem RowTemplate.scaleBalanced_parallel_factor_eq {m q : ℕ}
    (T : RowTemplate m q) (u v : Fin m) (huv : u ≠ v)
    (p : Fin (q + 2) → ℕ) (hp : ∀ i, p i ≠ 0)
    (hpar : (T.scaleBalancedP u v).Parallel (T.scaleBalancedQ u v)) :
    (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) =
      if T.support = {u} then (p 1 : ℚ) / (p 0 : ℚ) else
        if T.support = {v} then (p 0 : ℚ) / (p 1 : ℚ) else 1 := by
  classical
  let c : Fin m → ℚ := fun _ => 1
  let oldp := dropPrimeTuple2 p
  let z₀ : Fin m → ℤ := fun k => if k = T.anchor then 1 else 0
  let z₀Q : Fin m → ℚ := fun k => (z₀ k : ℚ)
  have hpOld : ∀ i, oldp i ≠ 0 := fun i => hp i.succ.succ
  have hOldEq : rowForm c T oldp z₀Q = T.value oldp T.anchor := by
    simpa [c, z₀, z₀Q] using rowForm_basis_anchor_eq_value c T oldp (by norm_num)
  have hOldNe : rowForm c T oldp z₀Q ≠ 0 := by
    rw [hOldEq]
    exact T.value_ne_zero_of_slots oldp T.anchor
      (Finset.max'_mem T.support T.support_nonempty) hpOld
  have hscale := RowTemplate.rowForm_eq_monomial_scale_of_parallel
    c (T.scaleBalancedP u v) (T.scaleBalancedQ u v) hpar p hp z₀Q
  rcases T.scaleBalancedBranches_parallel_support u v huv hpar with
    hnone | hsingleU | hsingleV
  · have hP : rowForm c (T.scaleBalancedP u v) p z₀Q = rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedP_tuple2 c T u v huv p z₀]
      calc
        rowForm c T oldp
            (Function.update (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u))
              v ((p 1 : ℚ) * z₀Q v)) =
            rowForm c T oldp (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)) :=
              rowForm_update_of_not_mem_support c T oldp
                (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)) v
                ((p 1 : ℚ) * z₀Q v) hnone.2
        _ = rowForm c T oldp z₀Q :=
              rowForm_update_of_not_mem_support c T oldp z₀Q u
                ((p 0 : ℚ) * z₀Q u) hnone.1
    have hQ : rowForm c (T.scaleBalancedQ u v) p z₀Q = rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedQ_tuple2 c T u v huv p z₀]
      calc
        rowForm c T oldp
            (Function.update (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v))
              u ((p 1 : ℚ) * z₀Q u)) =
            rowForm c T oldp (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v)) :=
              rowForm_update_of_not_mem_support c T oldp
                (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v)) u
                ((p 1 : ℚ) * z₀Q u) hnone.1
        _ = rowForm c T oldp z₀Q :=
              rowForm_update_of_not_mem_support c T oldp z₀Q v
                ((p 0 : ℚ) * z₀Q v) hnone.2
    have hfactor : (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) = 1 := by
      have hEq : rowForm c T oldp z₀Q =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * rowForm c T oldp z₀Q := by
        simpa [hP, hQ] using hscale
      exact mul_right_cancel₀ hOldNe (by simpa using hEq.symm)
    have hnotU : T.support ≠ {u} := by
      intro heq
      have : u ∈ T.support := by rw [heq]; simp
      exact hnone.1 this
    have hnotV : T.support ≠ {v} := by
      intro heq
      have : v ∈ T.support := by rw [heq]; simp
      exact hnone.2 this
    simp [hnotU, hnotV, hfactor]
  · have hvNot : v ∉ T.support := by
      rw [hsingleU]
      simp [Ne.symm huv]
    have hP : rowForm c (T.scaleBalancedP u v) p z₀Q =
        (p 0 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedP_tuple2 c T u v huv p z₀]
      calc
        rowForm c T oldp
            (Function.update (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u))
              v ((p 1 : ℚ) * z₀Q v)) =
            rowForm c T oldp (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)) :=
              rowForm_update_of_not_mem_support c T oldp
                (Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)) v
                ((p 1 : ℚ) * z₀Q v) hvNot
        _ = (p 0 : ℚ) * rowForm c T oldp z₀Q :=
              rowForm_update_mul_singleton c T oldp z₀Q u (p 0 : ℚ)
                hsingleU (by norm_num [c])
    have hQ : rowForm c (T.scaleBalancedQ u v) p z₀Q =
        (p 1 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedQ_tuple2 c T u v huv p z₀]
      let z₁ : Fin m → ℚ := Function.update z₀Q v ((p 0 : ℚ) * z₀Q v)
      have hzu : z₁ u = z₀Q u := by
        exact Function.update_of_ne huv _ _
      calc
        rowForm c T oldp (Function.update z₁ u ((p 1 : ℚ) * z₀Q u)) =
            rowForm c T oldp (Function.update z₁ u ((p 1 : ℚ) * z₁ u)) := by rw [hzu]
        _ = (p 1 : ℚ) * rowForm c T oldp z₁ :=
              rowForm_update_mul_singleton c T oldp z₁ u (p 1 : ℚ)
                hsingleU (by norm_num [c])
        _ = (p 1 : ℚ) * rowForm c T oldp z₀Q := by
              rw [rowForm_update_of_not_mem_support c T oldp z₀Q v
                ((p 0 : ℚ) * z₀Q v) hvNot]
    have hp0 : (p 0 : ℚ) ≠ 0 := by exact_mod_cast hp 0
    have hfactor : (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) =
        (p 1 : ℚ) / (p 0 : ℚ) := by
      have hEq : (p 1 : ℚ) * rowForm c T oldp z₀Q =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) *
            ((p 0 : ℚ) * rowForm c T oldp z₀Q) := by
        simpa [hP, hQ, mul_assoc] using hscale
      have hcancel : (p 1 : ℚ) =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (p 0 : ℚ) :=
        mul_right_cancel₀ hOldNe (by simpa [mul_assoc] using hEq)
      field_simp [hp0]
      nlinarith [hcancel]
    simp [hsingleU, hfactor, huv, Ne.symm huv]
  · have huNot : u ∉ T.support := by
      rw [hsingleV]
      simp [huv]
    have hP : rowForm c (T.scaleBalancedP u v) p z₀Q =
        (p 1 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedP_tuple2 c T u v huv p z₀]
      let z₁ : Fin m → ℚ := Function.update z₀Q u ((p 0 : ℚ) * z₀Q u)
      have hzv : z₁ v = z₀Q v := by exact Function.update_of_ne (Ne.symm huv) _ _
      calc
        rowForm c T oldp (Function.update z₁ v ((p 1 : ℚ) * z₀Q v)) =
            rowForm c T oldp (Function.update z₁ v ((p 1 : ℚ) * z₁ v)) := by rw [hzv]
        _ = (p 1 : ℚ) * rowForm c T oldp z₁ :=
              rowForm_update_mul_singleton c T oldp z₁ v (p 1 : ℚ)
                hsingleV (by norm_num [c])
        _ = (p 1 : ℚ) * rowForm c T oldp z₀Q := by
              rw [rowForm_update_of_not_mem_support c T oldp z₀Q u
                ((p 0 : ℚ) * z₀Q u) huNot]
    have hQ : rowForm c (T.scaleBalancedQ u v) p z₀Q =
        (p 0 : ℚ) * rowForm c T oldp z₀Q := by
      rw [rowForm_scaleBalancedQ_tuple2 c T u v huv p z₀]
      calc
        rowForm c T oldp
            (Function.update (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v))
              u ((p 1 : ℚ) * z₀Q u)) =
            rowForm c T oldp (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v)) :=
              rowForm_update_of_not_mem_support c T oldp
                (Function.update z₀Q v ((p 0 : ℚ) * z₀Q v)) u
                ((p 1 : ℚ) * z₀Q u) huNot
        _ = (p 0 : ℚ) * rowForm c T oldp z₀Q :=
              rowForm_update_mul_singleton c T oldp z₀Q v (p 0 : ℚ)
                hsingleV (by norm_num [c])
    have hp1 : (p 1 : ℚ) ≠ 0 := by exact_mod_cast hp 1
    have hfactor : (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) =
        (p 0 : ℚ) / (p 1 : ℚ) := by
      have hEq : (p 0 : ℚ) * rowForm c T oldp z₀Q =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) *
            ((p 1 : ℚ) * rowForm c T oldp z₀Q) := by
        simpa [hP, hQ, mul_assoc] using hscale
      have hcancel : (p 0 : ℚ) =
          (∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (p 1 : ℚ) :=
        mul_right_cancel₀ hOldNe (by simpa [mul_assoc] using hEq)
      field_simp [hp1]
      nlinarith [hcancel]
    have hnotU : T.support ≠ {u} := by
      intro heq
      have hvSupport : v ∈ T.support := by rw [hsingleV]; simp
      have hvMem : v ∈ ({u} : Finset (Fin m)) := by rw [← heq]; exact hvSupport
      have hvu : v = u := Finset.mem_singleton.mp hvMem
      exact huv hvu.symm
    simp [hsingleV, hnotU, hfactor, Ne.symm huv]

theorem chainWeight_scaleBalanced_invariant {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) {q : ℕ}
    (T : RowTemplate m q) (u v : Fin m) (huv : u ≠ v)
    (p : Fin (q + 2) → ℕ) (hp : ∀ i, p i ≠ 0)
    (hp₀ : (p 0).Prime) (hp₁ : (p 1).Prime)
    (hV₀ : masterScaleV S.core.parameters N C.gap < p 0)
    (hV₁ : masterScaleV S.core.parameters N C.gap < p 1)
    (hne : p 0 ≠ p 1)
    (hpar : (T.scaleBalancedP u v).Parallel (T.scaleBalancedQ u v))
    (y : ℤ)
    (hden : ((∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (y : ℚ)).den = 1) :
    chainWeight S.core.parameters C N d
      (((∏ i, (p i : ℚ) ^ (Classical.choose hpar.2 i)) * (y : ℚ)).num) =
        chainWeight S.core.parameters C N d y := by
  have hfactor := T.scaleBalanced_parallel_factor_eq u v huv p hp hpar
  rw [hfactor] at hden ⊢
  rcases T.scaleBalancedBranches_parallel_support u v huv hpar with
    hnone | hsingleU | hsingleV
  · have hnotU : T.support ≠ {u} := by
      intro heq
      have hu : u ∈ T.support := by rw [heq]; simp
      exact hnone.1 hu
    have hnotV : T.support ≠ {v} := by
      intro heq
      have hv : v ∈ T.support := by rw [heq]; simp
      exact hnone.2 hv
    simp only [hnotU, hnotV] at hden ⊢
    simp
  · have hnotV : T.support ≠ {v} := by
      intro heq
      have hu : u ∈ T.support := by rw [hsingleU]; simp
      rw [heq] at hu
      have huv' : u = v := Finset.mem_singleton.mp hu
      exact huv huv'
    simp only [if_pos hsingleU] at hden ⊢
    exact chainWeight_rat_div_mul_eq_of_prime_gt S C N d (p 1) (p 0)
      hp₁ hp₀ hV₁ hV₀ (Ne.symm hne) y hden
  · have hnotU : T.support ≠ {u} := by
      intro heq
      have hv : v ∈ T.support := by rw [hsingleV]; simp
      rw [heq] at hv
      have hvu : v = u := Finset.mem_singleton.mp hv
      exact (Ne.symm huv) hvu
    rw [if_neg hnotU] at hden ⊢
    simp only [if_pos hsingleV] at hden ⊢
    exact chainWeight_rat_div_mul_eq_of_prime_gt S C N d (p 0) (p 1)
      hp₀ hp₁ hV₀ hV₁ hne y hden

noncomputable def mergedBranchRowFunction {m q r r' : ℕ} {I : Fin r → Prop}
    (good : (Fin (q + 2) → ℕ) → Prop)
    (L R : Fin r → RowTemplate m (q + 2))
    (e : RowBranchIndex I ≃ Fin r')
    (hInv : ∀ i, I i ↔ (L i).Parallel (R i))
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (W : Fin r → ℤ → ℝ)
    (p : Fin (q + 2) → ℕ) (j : Fin r') (y : ℤ) : ℝ := by
  classical
  let x := e.symm j
  by_cases h : I x.val.1
  · by_cases hg : good p
    ·
      let hpar : (L x.val.1).Parallel (R x.val.1) := hInv x.val.1 |>.mp h
      exact combineParallelRowFunction (f x.val.1)
        (fun p' => RowTemplate.parallelScaleFactor (L x.val.1) (R x.val.1) hpar p')
        (W x.val.1) p y
    · exact 0
  · exact f x.val.1 (dropPrimeTuple2 p) y

theorem mergedBranchRowFunction_abs_le {m q r r' : ℕ} {I : Fin r → Prop}
    (good : (Fin (q + 2) → ℕ) → Prop)
    (L R : Fin r → RowTemplate m (q + 2))
    (e : RowBranchIndex I ≃ Fin r')
    (hInv : ∀ i, I i ↔ (L i).Parallel (R i))
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (W : Fin r → ℤ → ℝ)
    (p : Fin (q + 2) → ℕ)
    (hf : ∀ i p y, |f i p y| ≤ W i y)
    (hW : ∀ i y, 0 ≤ W i y) (hWpos : ∀ i y, 0 < W i y)
    (hinv : ∀ i (h : I i) (p : Fin (q + 2) → ℕ) (y : ℤ), good p →
      (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp h) p * (y : ℚ)).den = 1 →
      W i ((RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp h) p *
        (y : ℚ)).num) = W i y) (j : Fin r') (y : ℤ) :
    |mergedBranchRowFunction good L R e hInv f W p j y| ≤ W (e.symm j).val.1 y := by
  classical
  let x := e.symm j
  by_cases h : I x.val.1
  · by_cases hg : good p
    · have hInvRow := hInv x.val.1 |>.mp h
      have hBound := combineParallelRowFunction_abs_le (f x.val.1)
        (fun p' => RowTemplate.parallelScaleFactor (L x.val.1) (R x.val.1) hInvRow p')
        (W x.val.1) p
        (hW x.val.1) (hWpos x.val.1) (hf x.val.1)
        (fun y hden => hinv x.val.1 h p y hg hden)
      simpa [mergedBranchRowFunction, x, h, hg, hInvRow] using hBound y
    · simpa [mergedBranchRowFunction, x, h, hg] using hW x.val.1 y
  · simpa [mergedBranchRowFunction, x, h] using hf x.val.1 (dropPrimeTuple2 p) y

theorem pkgMask_mergedInvariantRow_eval {m q r r' : ℕ} {I : Fin r → Prop}
    (good : (Fin (q + 2) → ℕ) → Prop)
    (L R : Fin r → RowTemplate m (q + 2))
    (e : RowBranchIndex I ≃ Fin r')
    (hInv : ∀ i, I i ↔ (L i).Parallel (R i))
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (W : Fin r → ℤ → ℝ)
    (p : Fin (q + 2) → ℕ) (i : Fin r) (hi : I i) (hgood : good p)
    (c : Fin m → ℚ) (z : Fin m → ℚ) (y : ℤ)
    (hform : rowForm c (L i) p z = (y : ℚ))
    (hscaleDen :
      (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p *
        (y : ℚ)).den = 1)
    (hWpos : 0 < W i y) :
    W i y * atQ (mergedBranchRowFunction good L R e hInv f W p
        (e ⟨(i, 0), Or.inl rfl⟩)) (rowForm c (L i) p z) =
      f i (dropPrimeTuple2 p) y *
        f i (dropPrimeTuple2 p)
          (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p *
            (y : ℚ)).num := by
  let x : RowBranchIndex I := ⟨(i, 0), Or.inl rfl⟩
  have hmerged :
      mergedBranchRowFunction good L R e hInv f W p (e x) =
        combineParallelRowFunction (f i)
          (fun p' => RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p')
          (W i) p := by
    funext t
    unfold mergedBranchRowFunction
    simp only [Equiv.symm_apply_apply]
    simp [x, hi, hgood]
  rw [show (e x) = e ⟨(i, 0), Or.inl rfl⟩ by rfl, hmerged, hform]
  simp [atQ]
  unfold combineParallelRowFunction
  simp [atQ, hscaleDen]
  field_simp [ne_of_gt hWpos]

theorem pkgMask_mergedNonInvariantRow_eq {m q r r' : ℕ} {I : Fin r → Prop}
    (good : (Fin (q + 2) → ℕ) → Prop)
    (L R : Fin r → RowTemplate m (q + 2))
    (e : RowBranchIndex I ≃ Fin r')
    (hInv : ∀ i, I i ↔ (L i).Parallel (R i))
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (W : Fin r → ℤ → ℝ)
    (p : Fin (q + 2) → ℕ) (x : RowBranchIndex I) (hx : ¬ I x.val.1) :
    mergedBranchRowFunction good L R e hInv f W p (e x) =
      f x.val.1 (dropPrimeTuple2 p) := by
  funext y
  unfold mergedBranchRowFunction
  simp [Equiv.symm_apply_apply, hx]

theorem pkgMask_branchRowProductIdentity {m q r r' : ℕ} {I : Fin r → Prop}
    (Sh : RowShape m q r) (Sh' : RowShape m (q + 2) r')
    (L R : Fin r → RowTemplate m (q + 2))
    (e : RowBranchIndex I ≃ Fin r')
    (hInv : ∀ i, I i ↔ (L i).Parallel (R i))
    (hrow : ∀ x, Sh'.row (e x) =
      RowBranchTemplate Sh L R x.val.1 x.val.2)
    (good : (Fin (q + 2) → ℕ) → Prop)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (W : Fin r → ℤ → ℝ)
    (c : Fin m → ℚ) (p : Fin (q + 2) → ℕ) (hgood : good p) (z : Fin m → ℚ)
    (hp : ∀ j, p j ≠ 0)
    (hdenL : ∀ i, (rowForm c (L i) p z).den = 1)
    (hscaleDen : ∀ i (hi : I i),
      (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p *
        ((rowForm c (L i) p z).num : ℚ)).den = 1)
    (hWpos : ∀ i, 0 < W i (rowForm c (L i) p z).num) :
    (∏ i : Fin r, if hi : I i then
        W i (rowForm c (L i) p z).num else 1) *
      ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv f W p j)
        (rowForm c (Sh'.row j) p z) =
      (∏ i : Fin r, atQ (f i (dropPrimeTuple2 p)) (rowForm c (L i) p z)) *
        ∏ i : Fin r, atQ (f i (dropPrimeTuple2 p)) (rowForm c (R i) p z) := by
  classical
  letI : DecidablePred I := Classical.decPred I
  letI : Finite (RowBranchIndex I) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (RowBranchIndex I) := Fintype.ofFinite _
  letI : ∀ i : Fin r, Fintype (pkgMask_RowBranchAllowed I i) := fun i => by
    letI : DecidablePred (fun b : Fin 2 => b.val = 0 ∨ ¬ I i) := Classical.decPred _
    letI : Finite (pkgMask_RowBranchAllowed I i) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact Fintype.ofFinite _
  let branchEval : RowBranchIndex I → ℝ := fun x =>
    atQ (mergedBranchRowFunction good L R e hInv f W p (e x))
      (rowForm c (RowBranchTemplate Sh L R x.val.1 x.val.2) p z)
  let branchValue (i : Fin r) (b : pkgMask_RowBranchAllowed I i) : ℝ :=
    branchEval ⟨(i, b.val), b.property⟩
  let leftValue (i : Fin r) : ℝ :=
    atQ (f i (dropPrimeTuple2 p)) (rowForm c (L i) p z)
  let rightValue (i : Fin r) : ℝ :=
    atQ (f i (dropPrimeTuple2 p)) (rowForm c (R i) p z)
  have hshapeProd :
      (∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv f W p j)
        (rowForm c (Sh'.row j) p z)) = ∏ x : RowBranchIndex I, branchEval x := by
    calc
      _ = ∏ x : RowBranchIndex I,
          atQ (mergedBranchRowFunction good L R e hInv f W p (e x))
            (rowForm c (Sh'.row (e x)) p z) :=
        (Equiv.prod_comp e (fun j =>
          atQ (mergedBranchRowFunction good L R e hInv f W p j)
            (rowForm c (Sh'.row j) p z))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro x hx
        simp [branchEval, hrow x]
  have hbranchProd := pkgMask_rowBranchProduct_sigma I branchEval
  have hperRow (i : Fin r) :
      (if hi : I i then W i (rowForm c (L i) p z).num else 1) *
        ∏ b : pkgMask_RowBranchAllowed I i, branchValue i b =
          leftValue i * rightValue i := by
    rw [pkgMask_prodRowBranchAllowed I i (branchValue i)]
    by_cases hi : I i
    · simp [hi]
      let x0 : RowBranchIndex I := ⟨(i, 0), Or.inl rfl⟩
      have hform : rowForm c (L i) p z = ((rowForm c (L i) p z).num : ℚ) :=
        (Rat.den_eq_one_iff _).mp (hdenL i) |>.symm
      have hpar := (hInv i).mp hi
      have hrowScale := RowTemplate.rowForm_eq_monomial_scale_of_parallel
        c (L i) (R i) hpar p hp z
      have hRform : rowForm c (R i) p z =
          RowTemplate.parallelScaleFactor (L i) (R i) hpar p *
            ((rowForm c (L i) p z).num : ℚ) := by
        exact hrowScale.trans (congrArg
          (fun t : ℚ => RowTemplate.parallelScaleFactor (L i) (R i) hpar p * t) hform)
      have hleft : leftValue i = f i (dropPrimeTuple2 p)
          (rowForm c (L i) p z).num := by
        simp [leftValue, atQ, hdenL i]
      have hright : rightValue i = f i (dropPrimeTuple2 p)
          (RowTemplate.parallelScaleFactor (L i) (R i) hpar p *
            ((rowForm c (L i) p z).num : ℚ)).num := by
        dsimp [rightValue]
        rw [hRform]
        simp [atQ, hscaleDen i hi]
      have hInvEval := pkgMask_mergedInvariantRow_eval good L R e hInv f W p
        i hi hgood c z (rowForm c (L i) p z).num hform
        (hscaleDen i hi) (hWpos i)
      let b0 : pkgMask_RowBranchAllowed I i := ⟨0, Or.inl rfl⟩
      have hb0 : branchValue i ⟨0, Or.inl rfl⟩ =
          atQ (mergedBranchRowFunction good L R e hInv f W p (e x0))
            (rowForm c (L i) p z) := by
        change branchValue i b0 = _
        simp [branchValue, branchEval, b0, x0, RowBranchTemplate]
      rw [hb0]
      calc
        W i (rowForm c (L i) p z).num *
            atQ (mergedBranchRowFunction good L R e hInv f W p (e x0))
              (rowForm c (L i) p z) =
            f i (dropPrimeTuple2 p) (rowForm c (L i) p z).num *
              f i (dropPrimeTuple2 p)
                (RowTemplate.parallelScaleFactor (L i) (R i) hpar p *
                  ((rowForm c (L i) p z).num : ℚ)).num := hInvEval
        _ = leftValue i * rightValue i := by rw [hleft, hright]
    · simp [hi, one_mul]
      let x0 : RowBranchIndex I := ⟨(i, 0), Or.inl rfl⟩
      let x1 : RowBranchIndex I := ⟨(i, 1), Or.inr hi⟩
      let b0 : pkgMask_RowBranchAllowed I i := ⟨0, Or.inl rfl⟩
      let b1 : pkgMask_RowBranchAllowed I i := ⟨1, Or.inr hi⟩
      have hleft : branchValue i b0 = leftValue i := by
        dsimp [branchValue, branchEval, b0]
        rw [pkgMask_mergedNonInvariantRow_eq good L R e hInv f W p x0 hi]
        simp [leftValue, x0, RowBranchTemplate]
      have hright : branchValue i b1 = rightValue i := by
        dsimp [branchValue, branchEval, b1]
        rw [pkgMask_mergedNonInvariantRow_eq good L R e hInv f W p x1 hi]
        simp [rightValue, x1, RowBranchTemplate]
      rw [hleft, hright]
  calc
    (∏ i : Fin r, if hi : I i then W i (rowForm c (L i) p z).num else 1) *
        ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv f W p j)
          (rowForm c (Sh'.row j) p z) =
      (∏ i : Fin r, if hi : I i then W i (rowForm c (L i) p z).num else 1) *
        ∏ i : Fin r, ∏ b : pkgMask_RowBranchAllowed I i, branchValue i b := by
          rw [hshapeProd, hbranchProd]
    _ = ∏ i : Fin r,
          ((if hi : I i then W i (rowForm c (L i) p z).num else 1) *
            ∏ b : pkgMask_RowBranchAllowed I i, branchValue i b) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i : Fin r, leftValue i * rightValue i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hperRow i
    _ = (∏ i : Fin r, leftValue i) * ∏ i : Fin r, rightValue i :=
          Finset.prod_mul_distrib

theorem RowTemplate.poly_eval_eq_valueNat {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (k : Fin m) :
    evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) = T.valueNat p k := by
  cases h : T.entry k <;>
    simp [evalIntegerPolynomial, RowTemplate.poly, RowTemplate.valueNat, h,
      MvPolynomial.eval_monomial]

theorem evalIntegerPolynomial_rename {q s : ℕ} (ι : Fin q ↪ Fin s)
    (P : IntegerPolynomial q) (p : Fin s → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun i => (p (ι i) : ℤ)) := by
  unfold evalIntegerPolynomial
  exact MvPolynomial.eval_rename ι (fun i => (p i : ℤ)) P

theorem evalIntegerPolynomial_zmod_ne_zero {s : ℕ} (P : IntegerPolynomial s)
    (p : Fin s → ℕ) (v : ℕ) (hv : v.Prime)
    (havoid : ¬ (v : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ))) :
    (evalIntegerPolynomial P (fun i => (p i : ℤ)) : ZMod v) ≠ 0 := by
  intro hzero
  apply havoid
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (evalIntegerPolynomial P (fun i => (p i : ℤ))) v).mp hzero

theorem rowTemplate_minor_eval_eq {m q : ℕ} (T U : RowTemplate m q)
    (p : Fin q → ℕ) (j k : Fin m) :
    evalIntegerPolynomial
        (T.poly j * U.poly k - T.poly k * U.poly j)
        (fun i => (p i : ℤ)) =
      ((T.valueNat p j * U.valueNat p k : ℕ) : ℤ) -
      ((T.valueNat p k * U.valueNat p j : ℕ) : ℤ) := by
  calc
    evalIntegerPolynomial (T.poly j * U.poly k - T.poly k * U.poly j)
        (fun i => (p i : ℤ)) =
      evalIntegerPolynomial (T.poly j) (fun i => (p i : ℤ)) *
          evalIntegerPolynomial (U.poly k) (fun i => (p i : ℤ)) -
        evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) *
          evalIntegerPolynomial (U.poly j) (fun i => (p i : ℤ)) := by
            simp [evalIntegerPolynomial]
    _ = ((T.valueNat p j : ℕ) : ℤ) * ((U.valueNat p k : ℕ) : ℤ) -
        ((T.valueNat p k : ℕ) : ℤ) * ((U.valueNat p j : ℕ) : ℤ) := by
          rw [T.poly_eval_eq_valueNat, U.poly_eval_eq_valueNat,
            T.poly_eval_eq_valueNat, U.poly_eval_eq_valueNat]
    _ = _ := by push_cast; ring

theorem rowShape_minor_value_ne_zero_of_tests {m q r s : ℕ}
    (Sh : RowShape m q r) (ι : Fin q ↪ Fin s)
    (Dm : Finset (IntegerPolynomial s))
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (p : Fin s → ℕ) (v : ℕ) (hv : v.Prime)
    (havoid : ∀ Q ∈ Dm,
      ¬ (v : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))
    (R I : Fin r) (hRI : R ≠ I) :
    ∃ j k,
      (((Sh.row R).valueNat (fun i => p (ι i)) j : ℕ) : ZMod v) *
          (((Sh.row I).valueNat (fun i => p (ι i)) k : ℕ) : ZMod v) -
        (((Sh.row R).valueNat (fun i => p (ι i)) k : ℕ) : ZMod v) *
          (((Sh.row I).valueNat (fun i => p (ι i)) j : ℕ) : ZMod v) ≠ 0 := by
  obtain ⟨P, hP, j, k, hPform⟩ :=
    Sh.nonparallel_minor_mem_templateMinors R I hRI
  have hPlisted : MvPolynomial.rename ι P ∈ Dm := hlisted P hP
  have hEval :=
    evalIntegerPolynomial_zmod_ne_zero (MvPolynomial.rename ι P) p v hv
      (havoid (MvPolynomial.rename ι P) hPlisted)
  rw [evalIntegerPolynomial_rename ι P p] at hEval
  have hminor := rowTemplate_minor_eval_eq (Sh.row R) (Sh.row I)
    (fun i => p (ι i)) j k
  rw [hPform] at hEval
  rw [hminor] at hEval
  exact ⟨j, k, by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hEval⟩

theorem rowShapeLinearCoefficients_pairwise_independent_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm) :
    ∀ᶠ N in atTop, ∀ p, (∀ i,
      (S.primeStage.pool N C.gap).lower ≤ p i ∧
      p i < (S.primeStage.pool N C.gap).upper ∧ (p i).Prime) →
      ∀ v (hv : v.Prime), N + 1 < v → v ≤ masterScaleV S.core.parameters N C.gap →
      (∀ Q ∈ Dm, ¬ (v : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ))) →
      ∀ R I, R ≠ I →
        ∃ j k,
          FromArithmetic.rationalResidue v hv
              (rowShapeLinearCoefficients Sh ι
                (chainScale S.core.parameters C a N) N p R j) *
            FromArithmetic.rationalResidue v hv
              (rowShapeLinearCoefficients Sh ι
                (chainScale S.core.parameters C a N) N p I k) -
          FromArithmetic.rationalResidue v hv
              (rowShapeLinearCoefficients Sh ι
                (chainScale S.core.parameters C a N) N p R k) *
            FromArithmetic.rationalResidue v hv
              (rowShapeLinearCoefficients Sh ι
                (chainScale S.core.parameters C a N) N p I j) ≠ 0 := by
  filter_upwards [rowShapeLinearCoefficients_eq_intCast_eventually S C a ha Sh ι,
      chainScale_pos_eventually S C a ha,
      chainScale_ratio_den_one_eventually S C a ha,
      rowShapeScaleNumerator_unit_eventually S C a ha Sh,
      pool_lower_gt_masterScaleV_eventually S C.gap] with
    N hcoeff hpos hden hunit hpoolLower
  intro p hp v hv hNv hvV havoid R I hRI
  letI : Fact v.Prime := ⟨hv⟩
  obtain ⟨j, k, hminor⟩ :=
    rowShape_minor_value_ne_zero_of_tests Sh ι Dm hlisted p v hv havoid R I hRI
  let T := Sh.row R
  let U := Sh.row I
  let p' : Fin q → ℕ := fun i => p (ι i)
  let c := chainScale S.core.parameters C a N
  have hTa : c T.anchor ≠ 0 := ne_of_gt (hpos T.anchor)
  have hUa : c U.anchor ≠ 0 := ne_of_gt (hpos U.anchor)
  have hdenT : ∀ i, i ∈ T.support → (c i / c T.anchor).den = 1 := by
    intro i hi
    exact hden T.support T.support_nonempty i hi
  have hdenU : ∀ i, i ∈ U.support → (c i / c U.anchor).den = 1 := by
    intro i hi
    exact hden U.support U.support_nonempty i hi
  have hunitT : ∀ i, i ∈ T.support →
      ((c i / c T.anchor).num : ZMod v) ≠ 0 := by
    intro i hi
    exact hunit R i hi v hv hNv
  have hunitU : ∀ i, i ∈ U.support →
      ((c i / c U.anchor).num : ZMod v) ≠ 0 := by
    intro i hi
    exact hunit I i hi v hv hNv
  obtain ⟨F, hfactor, hF⟩ := rowTemplateIntegerMinor_factor c T U p' v hv
    hTa hUa hdenT hdenU hunitT hunitU j k
  have hminorInt :
      (((T.valueNat p' j * U.valueNat p' k : ℕ) : ℤ) -
        ((T.valueNat p' k * U.valueNat p' j : ℕ) : ℤ) : ZMod v) ≠ 0 := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hminor
  have hdetCast :
      ((rowTemplateIntegerCoefficient c T p' j *
          rowTemplateIntegerCoefficient c U p' k -
        rowTemplateIntegerCoefficient c T p' k *
          rowTemplateIntegerCoefficient c U p' j : ℤ) : ZMod v) ≠ 0 := by
    have hfactorCast := congrArg (fun z : ℤ => (z : ZMod v)) hfactor
    have heq :
        ((rowTemplateIntegerCoefficient c T p' j *
            rowTemplateIntegerCoefficient c U p' k -
          rowTemplateIntegerCoefficient c T p' k *
            rowTemplateIntegerCoefficient c U p' j : ℤ) : ZMod v) =
          (F : ZMod v) *
            (((T.valueNat p' j * U.valueNat p' k : ℕ) : ℤ) -
              ((T.valueNat p' k * U.valueNat p' j : ℕ) : ℤ) : ZMod v) := by
      simpa only [Int.cast_sub, Int.cast_mul] using hfactorCast
    rw [heq]
    exact mul_ne_zero hF hminorInt
  have hres (L : Fin r) (i : Fin m) :
      FromArithmetic.rationalResidue v hv
          (rowShapeLinearCoefficients Sh ι c N p L i) =
        ((rowTemplateIntegerCoefficient c (Sh.row L) p' i : ℤ) : ZMod v) := by
    rw [hcoeff p L i]
    rw [rationalResidue_intCast]
    rfl
  refine ⟨j, k, ?_⟩
  rw [hres R j, hres I k, hres R k, hres I j]
  simpa only [Int.cast_sub, Int.cast_mul] using hdetCast

theorem rowShapeLinearCoefficients_anchor_residue_ne_zero_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) :
    ∀ᶠ N in atTop, ∀ p R v (hv : v.Prime),
      N + 1 < v → v ≤ masterScaleV S.core.parameters N C.gap →
      (∀ i, (S.primeStage.pool N C.gap).lower ≤ p i ∧
        p i < (S.primeStage.pool N C.gap).upper ∧ (p i).Prime) →
      FromArithmetic.rationalResidue v hv
        (rowShapeLinearCoefficients Sh ι
          (chainScale S.core.parameters C a N) N p R (Sh.row R).anchor) ≠ 0 := by
  filter_upwards [chainScale_pos_eventually S C a ha,
      pool_lower_gt_masterScaleV_eventually S C.gap] with N hscale hpoolLower
  intro p R v hv hNv hvV hp
  let T := Sh.row R
  have hslot : ∀ i, ¬ v ∣ p (ι i) := by
    intro i hdiv
    have hpi := hp (ι i)
    have heq : v = p (ι i) :=
      (Nat.prime_dvd_prime_iff_eq hv hpi.2.2).mp hdiv
    have hlarge : masterScaleV S.core.parameters N C.gap < p (ι i) :=
      lt_of_lt_of_le hpoolLower hpi.1
    omega
  have hratio : (chainScale S.core.parameters C a N T.anchor) /
      (chainScale S.core.parameters C a N T.anchor) = 1 :=
    div_self (ne_of_gt (hscale T.anchor))
  have hcoef :
      rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N) N p R T.anchor =
        (T.valueNat (fun i => p (ι i)) T.anchor : ℚ) := by
    change (chainScale S.core.parameters C a N T.anchor /
        chainScale S.core.parameters C a N T.anchor) *
        T.value (fun i => p (ι i)) T.anchor = _
    rw [hratio, T.value_eq_valueNat]
    ring
  have hres :
      FromArithmetic.rationalResidue v hv
          (T.valueNat (fun i => p (ι i)) T.anchor : ℚ) =
        (T.valueNat (fun i => p (ι i)) T.anchor : ZMod v) := by
    simpa using rationalResidue_eq_num_of_den_one hv
      (T.valueNat (fun i => p (ι i)) T.anchor : ℚ) (by simp)
  rw [hcoef, hres]
  exact T.valueNat_cast_ne_zero_of_slot_not_dvd
    (fun i => p (ι i)) T.anchor v hv (Finset.max'_mem T.support T.support_nonempty) hslot

theorem rowForm_den_one_eventually {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∀ T : RowTemplate m q, ∀ p : Fin q → ℕ, ∀ z : Fin m → ℤ,
      (rowForm (chainScale S.core.parameters C a N) T p
        (fun k => (z k : ℚ))).den = 1 := by
  filter_upwards [chainScale_ratio_den_one_eventually S C a ha] with N hratio
  intro T p z
  let c := chainScale S.core.parameters C a N
  have hterm (k : Fin m) :
      c k / c T.anchor * T.value p k * (z k : ℚ) =
        (( (c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k : ℤ) : ℚ) := by
    cases hk : T.entry k with
    | none => simp [RowTemplate.value, RowTemplate.valueNat, hk]
    | some e =>
      have hmem : k ∈ T.support := by simp [RowTemplate.support, hk]
      have hden : (c k / c T.anchor).den = 1 := by
        exact hratio T.support T.support_nonempty k hmem
      have hnum : ((c k / c T.anchor).num : ℚ) = c k / c T.anchor :=
        (Rat.den_eq_one_iff _).mp hden
      calc
        c k / c T.anchor * T.value p k * (z k : ℚ) =
            ((c k / c T.anchor).num : ℚ) * (T.valueNat p k : ℚ) * (z k : ℚ) := by
          conv_lhs => rw [← hnum, T.value_eq_valueNat p k]
        _ = (((c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k : ℤ) : ℚ) := by
          rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  have hsum : rowForm c T p (fun k => (z k : ℚ)) =
      (((∑ k, (c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k) : ℤ) : ℚ) := by
    unfold rowForm
    calc
      (∑ k, c k / c T.anchor * T.value p k * (z k : ℚ)) =
          ∑ k, (((c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k : ℤ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
      _ = (((∑ k, (c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k) : ℤ) : ℚ) := by
        symm
        exact map_sum (Int.castRingHom ℚ)
          (fun k => (c k / c T.anchor).num * (T.valueNat p k : ℤ) * z k) Finset.univ
  rw [hsum]
  exact Rat.den_intCast _

theorem rowShapeLinearCoefficients_den_one_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) :
    ∀ᶠ N in atTop, ∀ p R k,
      (rowShapeLinearCoefficients Sh ι
        (chainScale S.core.parameters C a N) N p R k).den = 1 := by
  filter_upwards [chainScale_ratio_den_one_eventually S C a ha] with N hratio
  intro p R k
  let T := Sh.row R
  let c := chainScale S.core.parameters C a N
  by_cases hk : k ∈ T.support
  · have hden : (c k / c T.anchor).den = 1 :=
      hratio T.support T.support_nonempty k hk
    change ((c k / c T.anchor) * T.value (fun i => p (ι i)) k).den = 1
    rw [T.value_eq_valueNat, Rat.mul_den, hden]
    simp
  · have hnone : T.entry k = none := by
      cases h : T.entry k with
      | none => rfl
      | some e => exact (hk (by simp [RowTemplate.support, h])).elim
    change (c k / c T.anchor * T.value (fun i => p (ι i)) k).den = 1
    simp [RowTemplate.value, hnone]

theorem rowProduct_integrand_bound_eventually {K s m q r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) :
    ∀ N, ∀ f : Fin r → (Fin q → ℕ) → ℤ → ℝ,
      (∀ R p y, |f R p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
      ∀ (p : Fin q → ℕ) (z : Fin m → ℤ), |∏ R, atQ (f R p)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          (fun k => (z k : ℚ)))| ≤ (masterScaleV S.core.parameters N C.gap : ℝ) ^ (2 * r) := by
  intro N
  intro f hf p z
  have hVnat : 2 ≤ masterScaleV S.core.parameters N C.gap := by
    unfold masterScaleV
    omega
  have hV : (2 : ℝ) ≤ (masterScaleV S.core.parameters N C.gap : ℝ) := by
    exact_mod_cast hVnat
  have hOne : 1 + (masterScaleV S.core.parameters N C.gap : ℝ) ≤
      (masterScaleV S.core.parameters N C.gap : ℝ) ^ 2 := by
    nlinarith
  have hrow (R : Fin r) :
      |atQ (f R p) (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
        (fun k => (z k : ℚ)))| ≤ 1 + (masterScaleV S.core.parameters N C.gap : ℝ) := by
    let x := rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
      (fun k => (z k : ℚ))
    by_cases hx : x.den = 1
    · rw [atQ, if_pos hx]
      calc
        |f R p x.num| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor x.num :=
          hf R p x.num
        _ ≤ 1 + (masterScaleV S.core.parameters N C.gap : ℝ) := by
          have hweight := chainWeight_le_masterScaleV S C N (Sh.row R).anchor x.num
          simpa [add_comm] using add_le_add_left hweight 1
    · simp [atQ, x, hx]
      positivity
  calc
    |∏ R : Fin r, atQ (f R p)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          (fun k => (z k : ℚ)))| =
        ∏ R : Fin r, |atQ (f R p)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
            (fun k => (z k : ℚ)))| := Finset.abs_prod Finset.univ _
    _ ≤ ∏ R : Fin r, (1 + (masterScaleV S.core.parameters N C.gap : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro R hR
        positivity
      · intro R hR
        exact hrow R
    _ ≤ ∏ R : Fin r, (masterScaleV S.core.parameters N C.gap : ℝ) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro R hR
        positivity
      · intro R hR
        exact hOne
    _ = ((masterScaleV S.core.parameters N C.gap : ℝ) ^ 2) ^ r := by simp
    _ = (masterScaleV S.core.parameters N C.gap : ℝ) ^ (2 * r) := by
      rw [pow_mul]

theorem harmonicLaw_nonneg_of_normalizer_pos (X W : ℕ)
    (hNorm : 0 < harmonicNormalizer X W) (z : ℤ) : 0 ≤ harmonicLaw X W z := by
  by_cases h : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · simp [harmonicLaw, h]
    positivity
  · simp [harmonicLaw, h]

theorem pivotMass_nonneg {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (z : Fin m → ℤ) :
    0 ≤ pivotMass S.core.parameters C N z := by
  unfold pivotMass
  apply Finset.prod_nonneg
  intro k hk
  exact harmonicLaw_nonneg_of_normalizer_pos _ _
    (harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block k).1)) (z k)

def harmonicLawSupport (X W : ℕ) : Finset ℤ :=
  Finset.image (fun n : ℕ => (n : ℤ))
    ((Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W))

private theorem harmonicLaw_zero_of_not_mem_support (X W : ℕ) (z : ℤ)
    (hz : z ∉ harmonicLawSupport X W) : harmonicLaw X W z = 0 := by
  by_contra hne
  have hcond : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W := by
    by_contra hnot
    have : harmonicLaw X W z = 0 := by simp [harmonicLaw, hnot]
    exact hne this
  have hnmem : z.toNat ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨hcond.2.1, hcond.2.2.1⟩, hcond.2.2.2⟩
  apply hz
  have hmem := Finset.mem_image_of_mem (fun n : ℕ => (n : ℤ)) hnmem
  rw [Int.toNat_of_nonneg hcond.1] at hmem
  exact hmem

noncomputable def pivotMassSupport {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun k =>
    harmonicLawSupport (S.core.parameters.X N (C.block k).1) (primorial (N + 1))

noncomputable def pkgMask_coordinateSplit {m : ℕ} (u : Fin m) :
    (Fin m → ℤ) ≃ ℤ × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) := by
  refine
    { toFun := fun z => (z u, fun i => z i.1)
      invFun := fun x k =>
        if hk : k = u then x.1
        else x.2 ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hmem
    exact hk (Finset.mem_singleton.mp hmem)
  · intro z
    funext k
    by_cases hk : k = u <;> simp [hk]
  · intro x
    apply Prod.ext
    · simp
    · funext i
      have hnot : (i : Fin m) ≠ u := by
        intro hEq
        have hmem : (i : Fin m) ∈ ({u} : Finset (Fin m)) := by simp [hEq]
        exact (Finset.mem_filter.mp i.property).2 hmem
      simp [hnot]

noncomputable def pkgMask_coordinateJoin {m : ℕ} (u : Fin m) (y : ℤ)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) : Fin m → ℤ :=
  (pkgMask_coordinateSplit u).symm (y, w)

noncomputable def pkgMask_pivotRestMass {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) : ℝ :=
  ∏ i : finsetComplement ({u} : Finset (Fin m)),
    harmonicLaw (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1)) (w i)

theorem pkgMask_pivotRestMass_zero_of_not_mem {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ)
    (hw : w ∉ Fintype.piFinset fun i : finsetComplement ({u} : Finset (Fin m)) =>
      harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))) :
    pkgMask_pivotRestMass S C N u w = 0 := by
  have hnot : ¬ ∀ i : finsetComplement ({u} : Finset (Fin m)),
      w i ∈ harmonicLawSupport (S.core.parameters.X N (C.block i.1).1)
        (primorial (N + 1)) := by
    intro hall
    apply hw
    exact Fintype.mem_piFinset.mpr hall
  push_neg at hnot
  obtain ⟨i, hi⟩ := hnot
  unfold pkgMask_pivotRestMass
  exact Finset.prod_eq_zero (f := fun j : finsetComplement ({u} : Finset (Fin m)) =>
    harmonicLaw (S.core.parameters.X N (C.block j.1).1) (primorial (N + 1)) (w j))
    (Finset.mem_univ i) (harmonicLaw_zero_of_not_mem_support _ _ _ hi)

theorem pkgMask_coordinateJoin_at {m : ℕ} (u : Fin m) (y : ℤ)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) :
    pkgMask_coordinateJoin u y w u = y := by
  have h := (pkgMask_coordinateSplit u).apply_symm_apply (y, w)
  exact congrArg Prod.fst h

theorem pkgMask_coordinateJoin_other {m : ℕ} (u : Fin m) (y : ℤ)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ)
    (i : finsetComplement ({u} : Finset (Fin m))) :
    pkgMask_coordinateJoin u y w i.1 = w i := by
  have h := (pkgMask_coordinateSplit u).apply_symm_apply (y, w)
  exact congrFun (congrArg Prod.snd h) i

theorem pkgMask_pivotMass_coordinate_split {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m) (z : Fin m → ℤ) :
    pivotMass S.core.parameters C N z =
      harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) (z u) *
        ∏ i : finsetComplement ({u} : Finset (Fin m)),
          harmonicLaw (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1)) (z i.1) := by
  classical
  let Tcomp := finsetComplement ({u} : Finset (Fin m))
  have hdisj : Disjoint ({u} : Finset (Fin m)) Tcomp := by
    apply Finset.disjoint_left.mpr
    intro k hk hcomp
    exact (Finset.mem_filter.mp hcomp).2 hk
  have hunion : ({u} : Finset (Fin m)) ∪ Tcomp = Finset.univ := by
    ext k
    constructor
    · intro _
      exact Finset.mem_univ k
    · intro _
      by_cases hk : k = u
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr hk))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by
            intro hmem
            exact hk (Finset.mem_singleton.mp hmem)⟩))
  have hattach :
      (∏ k ∈ Tcomp,
        harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k)) =
      ∏ i : Tcomp,
        harmonicLaw (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1)) (z i.1) := by
    calc
      _ = ∏ i ∈ Tcomp.attach,
          harmonicLaw (S.core.parameters.X N (C.block i.1).1)
            (primorial (N + 1)) (z i.1) :=
        (Finset.prod_attach Tcomp fun k =>
          harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k)).symm
      _ = _ := by simp
  unfold pivotMass
  calc
    (∏ k : Fin m,
        harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k)) =
        ∏ k ∈ (Finset.univ : Finset (Fin m)),
          harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k) := by
      simp
    _ = ∏ k ∈ ({u} : Finset (Fin m)) ∪ Tcomp,
          harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k) := by
      rw [hunion]
    _ = (∏ k ∈ ({u} : Finset (Fin m)),
          harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k)) *
        ∏ k ∈ Tcomp,
          harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) (z k) :=
      Finset.prod_union hdisj
    _ = harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) (z u) *
        ∏ i : Tcomp,
          harmonicLaw (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1)) (z i.1) := by
      simp only [Finset.prod_singleton]
      rw [hattach]

private theorem pivotMass_zero_of_not_mem_support {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (z : Fin m → ℤ)
    (hz : z ∉ pivotMassSupport S C N) : pivotMass S.core.parameters C N z = 0 := by
  have hnot : ¬ ∀ k, z k ∈
      harmonicLawSupport (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) := by
    intro hall
    apply hz
    apply Fintype.mem_piFinset.mpr
    exact hall
  push_neg at hnot
  obtain ⟨k, hk⟩ := hnot
  unfold pivotMass
  exact Finset.prod_eq_zero (s := Finset.univ)
    (f := fun j => harmonicLaw (S.core.parameters.X N (C.block j).1)
      (primorial (N + 1)) (z j)) (Finset.mem_univ k)
    (harmonicLaw_zero_of_not_mem_support _ _ _ hk)

theorem pivotMass_summable {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) :
    Summable (pivotMass S.core.parameters C N) := by
  classical
  apply summable_of_ne_finset_zero (s := pivotMassSupport S C N)
  intro z hz
  exact pivotMass_zero_of_not_mem_support S C N z hz

theorem pivotMass_tsum_one {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) :
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z = 1 := by
  classical
  let D := pivotMassSupport S C N
  have htotal (k : Fin m) :
      ∑' z : ℤ, harmonicLaw (S.core.parameters.X N (C.block k).1)
        (primorial (N + 1)) z = 1 := by
    apply harmonicLaw_tsum_one_of_normalizer_pos
    · exact S.core.parameters.Xpos N (C.block k).1
    · exact harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
        (S.gapStage.valid_raw_cutoffs N (C.block k).1)
  have hcoordinate (k : Fin m) :
      (∑ z ∈ harmonicLawSupport (S.core.parameters.X N (C.block k).1)
        (primorial (N + 1)), harmonicLaw (S.core.parameters.X N (C.block k).1)
          (primorial (N + 1)) z) = 1 := by
    calc
      (∑ z ∈ harmonicLawSupport (S.core.parameters.X N (C.block k).1)
        (primorial (N + 1)), harmonicLaw (S.core.parameters.X N (C.block k).1)
          (primorial (N + 1)) z) =
          ∑' z : ℤ, harmonicLaw (S.core.parameters.X N (C.block k).1)
            (primorial (N + 1)) z := by
        symm
        apply tsum_eq_sum
        intro z hz
        exact harmonicLaw_zero_of_not_mem_support _ _ _ hz
      _ = 1 := htotal k
  have hfinite :
      (∑ z ∈ D, pivotMass S.core.parameters C N z) = 1 := by
    calc
      (∑ z ∈ D, pivotMass S.core.parameters C N z) =
          ∏ k, ∑ z ∈ harmonicLawSupport (S.core.parameters.X N (C.block k).1)
            (primorial (N + 1)), harmonicLaw (S.core.parameters.X N (C.block k).1)
              (primorial (N + 1)) z := by
        unfold D pivotMassSupport
        symm
        exact Finset.prod_univ_sum
          (t := fun k => harmonicLawSupport
            (S.core.parameters.X N (C.block k).1) (primorial (N + 1)))
          (f := fun k z => harmonicLaw (S.core.parameters.X N (C.block k).1)
            (primorial (N + 1)) z)
      _ = ∏ k, 1 := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hcoordinate k
      _ = 1 := by simp
  calc
    (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z) =
        ∑ z ∈ D, pivotMass S.core.parameters C N z := by
      apply tsum_eq_sum
      intro z hz
      exact pivotMass_zero_of_not_mem_support S C N z hz
    _ = 1 := hfinite

theorem pkgMask_pivotTsum_coordinate_split {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m) (F : (Fin m → ℤ) → ℝ) :
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F z =
      ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
        (∏ i : finsetComplement ({u} : Finset (Fin m)),
          harmonicLaw (S.core.parameters.X N (C.block i.1).1)
            (primorial (N + 1)) (w i)) *
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
            (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w) := by
  classical
  let Tcomp := finsetComplement ({u} : Finset (Fin m))
  let A := harmonicLawSupport (S.core.parameters.X N (C.block u).1) (primorial (N + 1))
  let B := Fintype.piFinset fun i : Tcomp =>
    harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))
  let D := pivotMassSupport S C N
  let e := pkgMask_coordinateSplit u
  let restMass : (∀ i : Tcomp, ℤ) → ℝ := fun w =>
    ∏ i : Tcomp, harmonicLaw (S.core.parameters.X N (C.block i.1).1)
      (primorial (N + 1)) (w i)
  have hRestZero (w : ∀ i : Tcomp, ℤ) (hw : w ∉ B) : restMass w = 0 := by
    have hnot : ¬ ∀ i : Tcomp,
        w i ∈ harmonicLawSupport (S.core.parameters.X N (C.block i.1).1)
          (primorial (N + 1)) := by
      intro hall
      apply hw
      exact Fintype.mem_piFinset.mpr hall
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    dsimp [restMass]
    exact Finset.prod_eq_zero (f := fun j : Tcomp =>
      harmonicLaw (S.core.parameters.X N (C.block j.1).1) (primorial (N + 1)) (w j))
      (Finset.mem_univ i) (harmonicLaw_zero_of_not_mem_support _ _ _ hi)
  have hDforward (z : Fin m → ℤ) (hz : z ∈ D) : e z ∈ A ×ˢ B := by
    apply Finset.mem_product.mpr
    constructor
    · exact (Fintype.mem_piFinset.mp hz) u
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (Fintype.mem_piFinset.mp hz) i.1
  have hDbackward (x : ℤ × (∀ i : Tcomp, ℤ)) (hx : x ∈ A ×ˢ B) :
      e.symm x ∈ D := by
    apply Fintype.mem_piFinset.mpr
    intro k
    by_cases hk : k = u
    · subst k
      have hcoords := e.apply_symm_apply x
      have hval : (e.symm x) u = x.1 := by
        exact congrArg Prod.fst hcoords
      rw [hval]
      exact (Finset.mem_product.mp hx).1
    · let i : Tcomp := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          intro hmem
          exact hk (Finset.mem_singleton.mp hmem)⟩⟩
      have hcoords := e.apply_symm_apply x
      have hval : (e.symm x) k = x.2 i := by
        exact congrFun (congrArg Prod.snd hcoords) i
      rw [hval]
      exact (Fintype.mem_piFinset.mp (Finset.mem_product.mp hx).2) i
  have hmassJoin (y : ℤ) (w : ∀ i : Tcomp, ℤ) :
      pivotMass S.core.parameters C N (pkgMask_coordinateJoin u y w) =
        harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
          restMass w := by
    rw [pkgMask_pivotMass_coordinate_split S C N u
      (pkgMask_coordinateJoin u y w)]
    rw [pkgMask_coordinateJoin_at u y w]
    apply congrArg (fun t : ℝ =>
      harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y * t)
    simp only [restMass]
    apply Finset.prod_congr rfl
    intro i hi
    rw [pkgMask_coordinateJoin_other u y w i]
  have hRightOuterZero (w : ∀ i : Tcomp, ℤ) (hw : w ∉ B) :
      restMass w * ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w) = 0 := by
    rw [hRestZero w hw]
    simp
  have hsum :
      (∑ z ∈ D, pivotMass S.core.parameters C N z * F z) =
        ∑ x ∈ A ×ˢ B,
          (harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) x.1 *
            restMass x.2) * F (pkgMask_coordinateJoin u x.1 x.2) := by
    apply Finset.sum_bij (fun z _ => e z)
    · intro z hz
      exact hDforward z hz
    · intro z hz z' hz' heq
      exact e.injective heq
    · intro x hx
      exact ⟨e.symm x, hDbackward x hx, e.apply_symm_apply x⟩
    · intro z hz
      have hcoords := e.symm_apply_apply z
      have hjoin : pkgMask_coordinateJoin u (e z).1 (e z).2 = z := by
        change e.symm ((e z).1, (e z).2) = z
        rw [show ((e z).1, (e z).2) = e z by cases e z <;> rfl]
        exact hcoords
      calc
        pivotMass S.core.parameters C N z * F z =
            pivotMass S.core.parameters C N (pkgMask_coordinateJoin u (e z).1 (e z).2) *
              F (pkgMask_coordinateJoin u (e z).1 (e z).2) := by rw [hjoin]
        _ = _ := by rw [hmassJoin]
  have hLeft :
      (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F z) =
        ∑ z ∈ D, pivotMass S.core.parameters C N z * F z := by
    apply tsum_eq_sum
    intro z hz
    simp [pivotMass_zero_of_not_mem_support S C N z hz]
  have hRight :
      (∑' w : ∀ i : Tcomp, ℤ, restMass w *
        ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
          (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w)) =
        ∑ w ∈ B, restMass w *
          ∑ y ∈ A, harmonicLaw (S.core.parameters.X N (C.block u).1)
            (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w) := by
    rw [tsum_eq_sum (s := B) hRightOuterZero]
    apply Finset.sum_congr rfl
    intro w hw
    rw [tsum_eq_sum (s := A) (fun y hy => by
      simp [harmonicLaw_zero_of_not_mem_support _ _ _ hy])]
  calc
    (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * F z) =
        ∑ w ∈ B, restMass w *
          ∑ y ∈ A, harmonicLaw (S.core.parameters.X N (C.block u).1)
            (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w) := by
      rw [hLeft, hsum]
      calc
        (∑ x ∈ A ×ˢ B,
            (harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) x.1 *
              restMass x.2) * F (pkgMask_coordinateJoin u x.1 x.2)) =
            ∑ y ∈ A, ∑ w ∈ B,
              harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
                restMass w * F (pkgMask_coordinateJoin u y w) := by
          exact Finset.sum_product' A B (fun y w =>
            harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
              restMass w * F (pkgMask_coordinateJoin u y w))
        _ = ∑ w ∈ B, restMass w *
              ∑ y ∈ A, harmonicLaw (S.core.parameters.X N (C.block u).1)
                (primorial (N + 1)) y * F (pkgMask_coordinateJoin u y w) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro w hw
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = _ := hRight.symm

theorem pkgMask_pivotRestMass_tsum_one {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m) :
    ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
      pkgMask_pivotRestMass S C N u w = 1 := by
  have hcoord :
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y = 1 := by
    apply harmonicLaw_tsum_one_of_normalizer_pos
    · exact S.core.parameters.Xpos N (C.block u).1
    · exact harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
        (S.gapStage.valid_raw_cutoffs N (C.block u).1)
  have hsplit :=
    (pkgMask_pivotTsum_coordinate_split S C N u (fun _ => 1)).symm
  calc
    (∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
        pkgMask_pivotRestMass S C N u w) =
        ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z := by
      simpa [pkgMask_pivotRestMass, hcoord] using hsplit
    _ = 1 := pivotMass_tsum_one S C N

theorem pkgMask_gapRestMass_tsum_one {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper) :
    ∑' x : (Fin q → ℕ) ×
        (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
      gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2 = 1 := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let B := Fintype.piFinset fun i : finsetComplement ({u} : Finset (Fin m)) =>
    harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))
  let D := P ×ˢ B
  have hPzero (p : Fin q → ℕ) (hp : p ∉ P) : gapSlotMass S C.gap N p = 0 := by
    unfold gapSlotMass
    exact independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  have hPsum : (∑ p ∈ P, gapSlotMass S C.gap N p) = 1 := by
    calc
      (∑ p ∈ P, gapSlotMass S C.gap N p) =
          ∑' p : Fin q → ℕ, gapSlotMass S C.gap N p := (tsum_eq_sum (s := P) hPzero).symm
      _ = 1 := gapSlotMass_tsum_one S C.gap N hMass
  have hBsum :
      (∑ w ∈ B, pkgMask_pivotRestMass S C N u w) = 1 := by
    calc
      (∑ w ∈ B, pkgMask_pivotRestMass S C N u w) =
          ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
            pkgMask_pivotRestMass S C N u w := by
        symm
        apply tsum_eq_sum
        intro w hw
        exact pkgMask_pivotRestMass_zero_of_not_mem S C N u w hw
      _ = 1 := pkgMask_pivotRestMass_tsum_one S C N u
  have hDzero (x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ)) (hx : x ∉ D) :
      gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2 = 0 := by
    by_cases hp : x.1 ∈ P
    · have hw : x.2 ∉ B := by
        intro hw
        exact hx (Finset.mem_product.mpr ⟨hp, hw⟩)
      rw [pkgMask_pivotRestMass_zero_of_not_mem S C N u x.2 hw]
      simp
    · rw [hPzero x.1 hp]
      simp
  have hfinite :
      (∑ x ∈ D, gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) = 1 := by
    calc
      (∑ x ∈ D, gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) =
          ∑ p ∈ P, ∑ w ∈ B,
            gapSlotMass S C.gap N p * pkgMask_pivotRestMass S C N u w := by
        dsimp [D]
        exact Finset.sum_product' P B (fun p w =>
          gapSlotMass S C.gap N p * pkgMask_pivotRestMass S C N u w)
      _ = (∑ p ∈ P, gapSlotMass S C.gap N p) *
          (∑ w ∈ B, pkgMask_pivotRestMass S C N u w) := by
        calc
          (∑ p ∈ P, ∑ w ∈ B,
              gapSlotMass S C.gap N p * pkgMask_pivotRestMass S C N u w) =
              ∑ p ∈ P, gapSlotMass S C.gap N p *
                (∑ w ∈ B, pkgMask_pivotRestMass S C N u w) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [← Finset.mul_sum]
          _ = _ := by rw [Finset.sum_mul]
      _ = 1 := by rw [hPsum, hBsum]; norm_num
  calc
    (∑' x : (Fin q → ℕ) ×
        (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
      gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) =
        ∑ x ∈ D, gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2 := by
      apply tsum_eq_sum
      intro x hx
      exact hDzero x hx
    _ = 1 := hfinite

theorem pkgMask_weightedError_tsum_le {α : Type*} [Countable α]
    (μ f : α → ℝ) (ε : ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hμsum : Summable μ) (hμtotal : ∑' a, μ a = 1)
    (hε : 0 ≤ ε) (hbound : ∀ a, |f a| ≤ ε) :
    |∑' a, μ a * f a| ≤ ε := by
  have hnormle (a : α) : ‖μ a * f a‖ ≤ μ a * ε := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ a)]
    exact mul_le_mul_of_nonneg_left (hbound a) (hμ a)
  have hprodSummable : Summable (fun a => μ a * f a) := by
    apply (hμsum.mul_right ε).of_norm_bounded
    exact hnormle
  calc
    |∑' a, μ a * f a| = ‖∑' a, μ a * f a‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' a, ‖μ a * f a‖ := norm_tsum_le_tsum_norm hprodSummable.norm
    _ ≤ ∑' a, μ a * ε := hprodSummable.norm.tsum_le_tsum hnormle
      (hμsum.mul_right ε)
    _ = ε := by rw [hμsum.tsum_mul_right ε, hμtotal]; ring

theorem pkgMask_gapRestMass_summable {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m) :
    Summable (fun x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) =>
        gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let B := Fintype.piFinset fun i : finsetComplement ({u} : Finset (Fin m)) =>
    harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))
  apply summable_of_ne_finset_zero (s := P ×ˢ B)
  intro x hx
  by_cases hp : x.1 ∈ P
  · have hw : x.2 ∉ B := by
      intro hw
      exact hx (Finset.mem_product.mpr ⟨hp, hw⟩)
    rw [pkgMask_pivotRestMass_zero_of_not_mem S C N u x.2 hw]
    simp
  · unfold gapSlotMass
    rw [independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) x.1 hp]
    simp

theorem pkgMask_gapRestAverage_error_le {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    (E : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ x, |E x| ≤ ε) :
    |∑' x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
        (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * E x| ≤ ε := by
  apply pkgMask_weightedError_tsum_le
    (μ := fun x => gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2)
    E ε
  · intro x
    apply mul_nonneg
    · unfold gapSlotMass independentPrimePoolMass
      exact Finset.prod_nonneg fun i _ =>
        primePoolLaw_nonneg (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper (x.1 i) hMass
    · unfold pkgMask_pivotRestMass
      apply Finset.prod_nonneg
      intro i hi
      exact harmonicLaw_nonneg_of_normalizer_pos _ _
        (harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
          (S.gapStage.valid_raw_cutoffs N (C.block i.1).1)) (x.2 i)
  · exact pkgMask_gapRestMass_summable S C N u
  · exact pkgMask_gapRestMass_tsum_one S C N u hMass
  · exact hε
  · exact hE

theorem pkgMask_gapRestTsum_fubini {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (F : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) → ℝ) :
    ∑' p : Fin q → ℕ, gapSlotMass S C.gap N p *
      ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
        pkgMask_pivotRestMass S C N u w * F (p, w) =
      ∑' x : (Fin q → ℕ) ×
        (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
        (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * F x := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let B := Fintype.piFinset fun i : finsetComplement ({u} : Finset (Fin m)) =>
    harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))
  let D := P ×ˢ B
  have hPzero (p : Fin q → ℕ) (hp : p ∉ P) : gapSlotMass S C.gap N p = 0 := by
    unfold gapSlotMass
    exact independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  have hBzero (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) (hw : w ∉ B) :
      pkgMask_pivotRestMass S C N u w = 0 :=
    pkgMask_pivotRestMass_zero_of_not_mem S C N u w hw
  have hOuterZero (p : Fin q → ℕ) (hp : p ∉ P) :
      gapSlotMass S C.gap N p *
        ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
          pkgMask_pivotRestMass S C N u w * F (p, w) = 0 := by
    rw [hPzero p hp]
    simp
  have hDzero (x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ)) (hx : x ∉ D) :
      (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * F x = 0 := by
    by_cases hp : x.1 ∈ P
    · have hw : x.2 ∉ B := by
        intro hw
        exact hx (Finset.mem_product.mpr ⟨hp, hw⟩)
      rw [hBzero x.2 hw]
      simp
    · rw [hPzero x.1 hp]
      simp
  calc
    (∑' p : Fin q → ℕ, gapSlotMass S C.gap N p *
        ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
          pkgMask_pivotRestMass S C N u w * F (p, w)) =
        ∑ p ∈ P, gapSlotMass S C.gap N p *
          ∑ w ∈ B, pkgMask_pivotRestMass S C N u w * F (p, w) := by
      rw [tsum_eq_sum (s := P) hOuterZero]
      apply Finset.sum_congr rfl
      intro p hp
      rw [tsum_eq_sum (s := B) (fun w hw => by rw [hBzero w hw]; simp)]
    _ = ∑ p ∈ P, ∑ w ∈ B,
          (gapSlotMass S C.gap N p * pkgMask_pivotRestMass S C N u w) * F (p, w) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = ∑ x ∈ D,
          (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * F x := by
      dsimp [D]
      symm
      exact Finset.sum_product' P B (fun p w =>
        (gapSlotMass S C.gap N p * pkgMask_pivotRestMass S C N u w) * F (p, w))
    _ = ∑' x : (Fin q → ℕ) ×
          (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
          (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * F x := by
      symm
      exact tsum_eq_sum (s := D) hDzero

theorem pkgMask_gapRestMass_mul_summable {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m)
    (F : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) → ℝ) :
    Summable (fun x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) =>
        (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) * F x) := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let B := Fintype.piFinset fun i : finsetComplement ({u} : Finset (Fin m)) =>
    harmonicLawSupport (S.core.parameters.X N (C.block i.1).1) (primorial (N + 1))
  let D := P ×ˢ B
  have hPzero (p : Fin q → ℕ) (hp : p ∉ P) : gapSlotMass S C.gap N p = 0 := by
    unfold gapSlotMass
    exact independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  apply summable_of_ne_finset_zero (s := D)
  intro x hx
  by_cases hp : x.1 ∈ P
  · have hw : x.2 ∉ B := by
      intro hw
      exact hx (Finset.mem_product.mpr ⟨hp, hw⟩)
    rw [pkgMask_pivotRestMass_zero_of_not_mem S C N u x.2 hw]
    simp
  · rw [hPzero x.1 hp]
    simp

theorem pivotBaseResidueLaw_eq_prod_harmonicResidueLaw
    {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N modulus : ℕ)
    (hmodulus : 0 < modulus) (r : Fin m → Fin modulus) :
    FromArithmetic.baseResidueLaw modulus hmodulus (pivotMass S.core.parameters C N) r =
      ∏ i, harmonicResidueLaw
        (harmonicLaw (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
        modulus (r i) := by
  classical
  let D := pivotMassSupport S C N
  let coord (i : Fin m) (z : ℤ) : ℝ :=
    harmonicLaw (S.core.parameters.X N (C.block i).1) (primorial (N + 1)) z *
      (if FromArithmetic.integerResidue modulus hmodulus z = r i then 1 else 0)
  have hterm (z : Fin m → ℤ) :
      pivotMass S.core.parameters C N z *
        (if (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r
          then 1 else 0) = ∏ i, coord i (z i) := by
    have hvec :
        (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r ↔
          ∀ i, FromArithmetic.integerResidue modulus hmodulus (z i) = r i := by
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        exact funext h
    have hind :
        (if (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r
          then (1 : ℝ) else 0) =
          ∏ i, (if FromArithmetic.integerResidue modulus hmodulus (z i) = r i
            then (1 : ℝ) else 0) := by
      simp only [hvec]
      by_cases hall : ∀ i,
          FromArithmetic.integerResidue modulus hmodulus (z i) = r i
      · simp [hall]
      · have hnot : ¬ ∀ i,
            FromArithmetic.integerResidue modulus hmodulus (z i) = r i := hall
        obtain ⟨i, hi⟩ := not_forall.mp hnot
        have hzero :
            (∏ i, (if FromArithmetic.integerResidue modulus hmodulus (z i) = r i
              then (1 : ℝ) else 0)) = 0 :=
          Finset.prod_eq_zero (s := Finset.univ)
            (f := fun i => if FromArithmetic.integerResidue modulus hmodulus (z i) = r i
              then (1 : ℝ) else 0) (Finset.mem_univ i) (by simp [hi])
        rw [if_neg hnot, hzero]
    change (∏ i,
        harmonicLaw (S.core.parameters.X N (C.block i).1)
          (primorial (N + 1)) (z i)) * _ = _
    rw [hind, ← Finset.prod_mul_distrib]

  have hzero (z : Fin m → ℤ) (hz : z ∉ D) :
      pivotMass S.core.parameters C N z *
        (if (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r
          then 1 else 0) = 0 := by
    have hmass : pivotMass S.core.parameters C N z = 0 :=
      pivotMass_zero_of_not_mem_support S C N z (by simpa [D] using hz)
    simp [hmass]

  have hfinite :
      FromArithmetic.baseResidueLaw modulus hmodulus
          (pivotMass S.core.parameters C N) r =
        ∑ z ∈ D, ∏ i, coord i (z i) := by
    unfold FromArithmetic.baseResidueLaw
    calc
      (∑' z : Fin m → ℤ,
        pivotMass S.core.parameters C N z *
          (if (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r
            then 1 else 0)) =
          ∑ z ∈ D,
            pivotMass S.core.parameters C N z *
              (if (fun i => FromArithmetic.integerResidue modulus hmodulus (z i)) = r
                then 1 else 0) := tsum_eq_sum (s := D) hzero
      _ = ∑ z ∈ D, ∏ i, coord i (z i) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hterm z

  have hfactor :
      (∑ z ∈ D, ∏ i, coord i (z i)) =
        ∏ i, ∑ z ∈ harmonicLawSupport
            (S.core.parameters.X N (C.block i).1) (primorial (N + 1)), coord i z := by
    dsimp [D, pivotMassSupport]
    symm
    exact Finset.prod_univ_sum
      (t := fun i => harmonicLawSupport
        (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
      (f := fun i z => coord i z)

  have hcoordinate (i : Fin m) :
      (∑ z ∈ harmonicLawSupport
        (S.core.parameters.X N (C.block i).1) (primorial (N + 1)), coord i z) =
      harmonicResidueLaw
        (harmonicLaw (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
        modulus (r i) := by
    let X := S.core.parameters.X N (C.block i).1
    let W := primorial (N + 1)
    let supp := harmonicLawSupport X W
    have hnonneg (z : ℤ) (hz : z ∈ supp) : 0 ≤ z := by
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      exact Int.natCast_nonneg n
    have hres (z : ℤ) (hz : z ∈ supp) :
        FromArithmetic.integerResidue modulus hmodulus z = r i ↔
          0 ≤ z ∧ z.toNat % modulus = (r i).val := by
      constructor
      · intro heq
        have hval := congrArg Fin.val heq
        rw [integerResidue_eq_natMod_of_nonneg hmodulus (hnonneg z hz)] at hval
        exact ⟨hnonneg z hz, hval⟩
      · rintro ⟨hz0, hrem⟩
        apply Fin.ext
        rw [integerResidue_eq_natMod_of_nonneg hmodulus hz0]
        exact hrem
    have htermEq (z : ℤ) (hz : z ∈ supp) :
        coord i z =
          (if 0 ≤ z ∧ z.toNat % modulus = (r i).val then
            harmonicLaw X W z else 0) := by
      by_cases hc : 0 ≤ z ∧ z.toNat % modulus = (r i).val
      · have hr := (hres z hz).2 hc
        simp [coord, X, W, hc, hr]
      · have hr : ¬ FromArithmetic.integerResidue modulus hmodulus z = r i := by
          intro hr
          exact hc ((hres z hz).1 hr)
        simp [coord, X, W, hc, hr]
    have hzero (z : ℤ) (hz : z ∉ supp) :
        (if 0 ≤ z ∧ z.toNat % modulus = (r i).val then harmonicLaw X W z else 0) = 0 := by
      by_cases hc : 0 ≤ z ∧ z.toNat % modulus = (r i).val
      · simp [hc, harmonicLaw_zero_of_not_mem_support X W z hz]
      · simp [hc]
    unfold harmonicResidueLaw
    calc
      (∑ z ∈ supp, coord i z) =
          ∑ z ∈ supp,
            (if 0 ≤ z ∧ z.toNat % modulus = (r i).val then
              harmonicLaw X W z else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact htermEq z hz
      _ = ∑' z : ℤ,
          (if 0 ≤ z ∧ z.toNat % modulus = (r i).val then
            harmonicLaw X W z else 0) := (tsum_eq_sum (s := supp) hzero).symm

  calc
    FromArithmetic.baseResidueLaw modulus hmodulus
        (pivotMass S.core.parameters C N) r =
        ∑ z ∈ D, ∏ i, coord i (z i) := hfinite
    _ = ∏ i, ∑ z ∈ harmonicLawSupport
        (S.core.parameters.X N (C.block i).1) (primorial (N + 1)), coord i z := hfactor
    _ = ∏ i, harmonicResidueLaw
        (harmonicLaw (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
        modulus (r i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hcoordinate i

theorem harmonicResidueLaw_nonneg (X W modulus : ℕ)
    (hNorm : 0 < harmonicNormalizer X W) (a : Fin modulus) :
    0 ≤ harmonicResidueLaw (harmonicLaw X W) modulus a := by
  unfold harmonicResidueLaw
  apply tsum_nonneg
  intro z
  split_ifs
  · exact harmonicLaw_nonneg_of_normalizer_pos X W hNorm z
  · positivity

theorem harmonicResidueLaw_sum_one (X W modulus : ℕ) (hmodulus : 0 < modulus)
    (hX : 0 < X) (hNorm : 0 < harmonicNormalizer X W) :
    ∑ a : Fin modulus, harmonicResidueLaw (harmonicLaw X W) modulus a = 1 := by
  classical
  let supp := harmonicLawSupport X W
  have hzero (a : Fin modulus) (z : ℤ) (hz : z ∉ supp) :
      (if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) = 0 := by
    by_cases hc : 0 ≤ z ∧ z.toNat % modulus = a.val
    · simp [hc, harmonicLaw_zero_of_not_mem_support X W z hz]
    · simp [hc]
  have hfinite (a : Fin modulus) :
      harmonicResidueLaw (harmonicLaw X W) modulus a =
        ∑ z ∈ supp,
          (if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) := by
    unfold harmonicResidueLaw
    exact tsum_eq_sum (s := supp) (hzero a)
  have hfiber (z : ℤ) (hz : z ∈ supp) :
      ∑ a : Fin modulus,
        (if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) =
          harmonicLaw X W z := by
    have hznonneg : 0 ≤ z := by
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      exact Int.natCast_nonneg n
    let a₀ : Fin modulus := ⟨z.toNat % modulus, Nat.mod_lt _ hmodulus⟩
    have hcond (a : Fin modulus) :
        (0 ≤ z ∧ z.toNat % modulus = a.val) ↔ a = a₀ := by
      constructor
      · intro h
        apply Fin.ext
        simpa [a₀] using h.2.symm
      · intro h
        subst a
        exact ⟨hznonneg, rfl⟩
    calc
      (∑ a : Fin modulus,
        if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) =
        ∑ a : Fin modulus, if a = a₀ then harmonicLaw X W z else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [hcond]
      _ = harmonicLaw X W z := by simp
  calc
    (∑ a : Fin modulus, harmonicResidueLaw (harmonicLaw X W) modulus a) =
        ∑ a : Fin modulus, ∑ z ∈ supp,
          (if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hfinite a
    _ = ∑ z ∈ supp, ∑ a : Fin modulus,
          (if 0 ≤ z ∧ z.toNat % modulus = a.val then harmonicLaw X W z else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ supp, harmonicLaw X W z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hfiber z hz
    _ = ∑' z : ℤ, harmonicLaw X W z := by
      symm
      apply tsum_eq_sum (s := supp)
      intro z hz
      exact harmonicLaw_zero_of_not_mem_support X W z hz
    _ = 1 := harmonicLaw_tsum_one_of_normalizer_pos X W hX hNorm

theorem sourceParameter_M_tendsto_atTop {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) : Tendsto A.M atTop atTop := by
  have hpow : ∀ N : ℕ, N + 1 ≤ 2 ^ (N + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      calc
        N + 1 + 1 ≤ 2 * (N + 1) := by omega
        _ = (N + 1) * 2 := by omega
        _ ≤ 2 ^ (N + 1) * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ (N + 1 + 1) := by
          simp [pow_succ, Nat.add_assoc, Nat.mul_assoc]
  have hMbound : ∀ᶠ N in atTop, N ≤ A.M N := by
    filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    have hprime : Nat.Prime 2 := by norm_num
    have hdivW : 2 ∣ primorial (N + 1) :=
      hprime.dvd_primorial_iff.mpr (by omega)
    have hW : 2 ≤ primorial (N + 1) :=
      Nat.le_of_dvd (primorial_pos (N + 1)) hdivW
    have hpowW : 2 ^ (N + 1) ≤ primorial (N + 1) ^ (N + 1) :=
      Nat.pow_le_pow_left hW (N + 1)
    have hpowM : primorial (N + 1) ^ (N + 1) ≤ A.M N :=
      Nat.le_of_dvd (A.Mpos N) (A.Mdiv N)
    exact (Nat.le_succ N).trans ((hpow N).trans (hpowW.trans hpowM))
  exact tendsto_atTop_mono' atTop hMbound tendsto_id

theorem masterScaleV_tendsto_atTop {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l : Fin n) :
    Tendsto (fun N => masterScaleV A N l) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (sourceParameter_M_tendsto_atTop A)
  filter_upwards with N
  unfold masterScaleV
  omega

theorem masterScaleV_le_earlierScale_sq {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l i : Fin n) (hli : l < i) (N : ℕ) :
    (masterScaleV A N l : ℝ) ≤
      (OAI.AdmissibleMicrocellBoundary.earlierScale A.M
        (fun N => OAI.SourceAdmissible.previous (A.X N) i) N) ^ 2 := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter (fun j => j < l)
  let J : Finset (Fin n) := Finset.univ.filter (fun j => j < i)
  have hsub : I ⊆ J := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, lt_trans hj'.2 hli⟩
  have hprod :
      (∏ j ∈ I, A.X N j ^ 2) ≤
        (OAI.SourceAdmissible.previous (A.X N) i) ^ 2 := by
    calc
      (∏ j ∈ I, A.X N j ^ 2) ≤ ∏ j ∈ J, A.X N j ^ 2 :=
        Finset.prod_le_prod_of_subset_of_one_le hsub (by
          intro j hj hjnot
          exact Nat.one_le_pow 2 (A.X N j) (A.Xpos N j))
      _ = (OAI.SourceAdmissible.previous (A.X N) i) ^ 2 := by
        simp [J, OAI.SourceAdmissible.previous, Finset.prod_pow]
  have hprodR :
      ((∏ j ∈ I, A.X N j ^ 2 : ℕ) : ℝ) ≤
        ((OAI.SourceAdmissible.previous (A.X N) i : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hprod
  have hmain :
      (2 : ℝ) + (A.M N : ℝ) +
          ((∏ j ∈ I, A.X N j ^ 2 : ℕ) : ℝ) ≤
        (2 + (A.M N : ℝ) +
          ((OAI.SourceAdmissible.previous (A.X N) i : ℕ) : ℝ)) ^ 2 := by
    nlinarith [hprodR, Nat.cast_nonneg (α := ℝ) (A.M N),
      Nat.cast_nonneg (α := ℝ) (OAI.SourceAdmissible.previous (A.X N) i)]
  simpa [masterScaleV, I, OAI.AdmissibleMicrocellBoundary.earlierScale] using hmain

theorem logPivot_dominates_masterScaleV {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l i : Fin n) (hli : l < i) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N i : ℝ))
      (fun N => (masterScaleV A N l : ℝ)) := by
  intro B hB
  let E : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale A.M
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hEtop : Tendsto E atTop atTop := by
    have hM : Tendsto (fun N => (A.M N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (sourceParameter_M_tendsto_atTop A)
    apply tendsto_atTop_mono' atTop ?_ hM
    filter_upwards with N
    dsimp [E, OAI.AdmissibleMicrocellBoundary.earlierScale]
    nlinarith [Nat.cast_nonneg (α := ℝ) (OAI.SourceAdmissible.previous (A.X N) i)]
  have hEpos (N : ℕ) : 0 < E N := by
    dsimp [E, OAI.AdmissibleMicrocellBoundary.earlierScale]
    positivity
  have hlogH : Tendsto
      (fun N => Real.log (A.X N i : ℝ) / (A.H N i : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using A.Xdom i 1 (by norm_num)
  have hHE : Tendsto
      (fun N => (A.H N i : ℝ) / E N ^ (2 * B + 1)) atTop atTop := by
    simpa [E] using A.Hdom i (2 * B + 1) (by positivity)
  have hHEscaled : Tendsto
      (fun N => (A.H N i : ℝ) / E N ^ (2 * B)) atTop atTop := by
    have hmul := hHE.atTop_mul_atTop₀ hEtop
    have hEq : (fun N => (A.H N i : ℝ) / E N ^ (2 * B)) =
        fun N => ((A.H N i : ℝ) / E N ^ (2 * B + 1)) * E N := by
      funext N
      have hpow : E N ^ (2 * B + 1) = E N ^ (2 * B) * E N := by
        rw [Real.rpow_add (hEpos N)]
        simp
      rw [hpow]
      field_simp [ne_of_gt (hEpos N)]
    rw [hEq]
    exact hmul
  have hHV : Tendsto
      (fun N => (A.H N i : ℝ) / (masterScaleV A N l : ℝ) ^ B) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hHEscaled
    filter_upwards with N
    have hVle := masterScaleV_le_earlierScale_sq A l i hli N
    have hVpow : (masterScaleV A N l : ℝ) ^ B ≤ E N ^ (2 * B) := by
      calc
        (masterScaleV A N l : ℝ) ^ B ≤ (E N ^ 2) ^ B :=
          Real.rpow_le_rpow (by positivity) hVle hB.le
        _ = E N ^ (2 * B) := by
          calc
            (E N ^ (2 : ℕ) : ℝ) ^ B = (E N ^ (2 : ℝ)) ^ B := by
              exact congrArg (fun x : ℝ => x ^ B)
                (Real.rpow_natCast (E N) 2).symm
            _ = E N ^ (2 * B) :=
              (Real.rpow_mul (le_of_lt (hEpos N)) (2 : ℝ) B).symm
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (by
        have hV : 0 < masterScaleV A N l := by
          unfold masterScaleV
          omega
        exact_mod_cast hV) B) hVpow
  have hmul := hlogH.atTop_mul_atTop₀ hHV
  have hfinalEq :
      (fun N => Real.log (A.X N i : ℝ) / (masterScaleV A N l : ℝ) ^ B) =
        fun N => (Real.log (A.X N i : ℝ) / (A.H N i : ℝ)) *
          ((A.H N i : ℝ) / (masterScaleV A N l : ℝ) ^ B) := by
    funext N
    have hHpos : 0 < (A.H N i : ℝ) := by exact_mod_cast A.Hpos N i
    field_simp [ne_of_gt hHpos]
  rw [hfinalEq]
  exact hmul

theorem samplingInput_le_masterScaleV_pow {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l : Fin n) (r N : ℕ) :
    2 + primorial (N + 1) + (masterScaleV A N l) ^ r + 1 +
        masterScaleV A N l ≤ (masterScaleV A N l) ^ (r + 8) := by
  have hV : 2 ≤ masterScaleV A N l := by
    unfold masterScaleV
    omega
  have hW : primorial (N + 1) ≤ masterScaleV A N l := by
    calc
      primorial (N + 1) ≤ A.M N := A.Wle N
      _ ≤ masterScaleV A N l := by unfold masterScaleV; omega
  have hP : 1 ≤ (masterScaleV A N l) ^ (r + 5) := by
    exact Nat.one_le_pow _ _ (by omega : 0 < masterScaleV A N l)
  have hVleP : masterScaleV A N l ≤ (masterScaleV A N l) ^ (r + 5) := by
    calc
      masterScaleV A N l = (masterScaleV A N l) ^ 1 := by simp
      _ ≤ (masterScaleV A N l) ^ (r + 5) :=
        Nat.pow_le_pow_right (by omega : 0 < masterScaleV A N l) (by omega)
  have hRleP : (masterScaleV A N l) ^ r ≤ (masterScaleV A N l) ^ (r + 5) :=
    Nat.pow_le_pow_right (by omega : 0 < masterScaleV A N l) (by omega)
  have hTle :
      2 + primorial (N + 1) + (masterScaleV A N l) ^ r + 1 +
          masterScaleV A N l ≤ 6 * (masterScaleV A N l) ^ (r + 5) := by
    omega
  have h6 : 6 ≤ (masterScaleV A N l) ^ 3 := by
    have hpow : 2 ^ 3 ≤ (masterScaleV A N l) ^ 3 := Nat.pow_le_pow_left hV 3
    norm_num at hpow
    omega
  calc
    2 + primorial (N + 1) + (masterScaleV A N l) ^ r + 1 +
        masterScaleV A N l ≤ 6 * (masterScaleV A N l) ^ (r + 5) := hTle
    _ ≤ (masterScaleV A N l) ^ 3 * (masterScaleV A N l) ^ (r + 5) :=
      Nat.mul_le_mul_right _ h6
    _ = (masterScaleV A N l) ^ (r + 8) := by
      rw [← pow_add]
      congr 1 <;> omega

theorem logPivot_dominates_samplingInput {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l i : Fin n) (hli : l < i) (r : ℕ) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N i : ℝ))
      (fun N => (2 + primorial (N + 1) + (masterScaleV A N l) ^ r +
        1 + masterScaleV A N l : ℝ)) := by
  intro B hB
  have hlarge := logPivot_dominates_masterScaleV A l i hli
    (((r + 8 : ℕ) : ℝ) * B) (by positivity)
  have hVpos (N : ℕ) : 0 < (masterScaleV A N l : ℝ) := by
    have hV : 2 ≤ masterScaleV A N l := by unfold masterScaleV; omega
    exact_mod_cast (show 0 < masterScaleV A N l by omega)
  have hTpos (N : ℕ) :
      0 < (2 + primorial (N + 1) + (masterScaleV A N l) ^ r +
        1 + masterScaleV A N l : ℝ) := by positivity
  have hTbound (N : ℕ) :
      (2 + primorial (N + 1) + (masterScaleV A N l) ^ r +
        1 + masterScaleV A N l : ℝ) ≤
        (masterScaleV A N l : ℝ) ^ (r + 8 : ℕ) := by
    exact_mod_cast samplingInput_le_masterScaleV_pow A l r N
  have hTpow (N : ℕ) :
      (2 + primorial (N + 1) + (masterScaleV A N l) ^ r +
        1 + masterScaleV A N l : ℝ) ^ B ≤
        (masterScaleV A N l : ℝ) ^ (((r + 8 : ℕ) : ℝ) * B) := by
    calc
      _ ≤ ((masterScaleV A N l : ℝ) ^ (r + 8 : ℕ)) ^ B :=
        Real.rpow_le_rpow (by positivity) (hTbound N) hB.le
      _ = (masterScaleV A N l : ℝ) ^ (((r + 8 : ℕ) : ℝ) * B) := by
        calc
          ((masterScaleV A N l : ℝ) ^ (r + 8 : ℕ)) ^ B =
              ((masterScaleV A N l : ℝ) ^ ((r + 8 : ℕ) : ℝ)) ^ B :=
            congrArg (fun x : ℝ => x ^ B)
              (Real.rpow_natCast (masterScaleV A N l : ℝ) (r + 8)).symm
          _ = _ := (Real.rpow_mul (le_of_lt (hVpos N)) _ _).symm
  apply tendsto_atTop_mono' atTop ?_ hlarge
  filter_upwards with N
  have hXpos : 0 < (A.X N i : ℝ) := by exact_mod_cast A.Xpos N i
  have hlogNonneg : 0 ≤ Real.log (A.X N i : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt (A.Xpos N i)))
  exact div_le_div_of_nonneg_left hlogNonneg
    (Real.rpow_pos_of_pos (hTpos N) B) (hTpow N)

theorem pivot_sampling_log_condition_eventually {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (i : Fin m) :
    ∀ᶠ N in atTop,
      Real.log (S.core.parameters.X N (C.block i).1 : ℝ) >
        (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1 := by
  have hratio : Tendsto
      (fun N => Real.log (S.core.parameters.X N (C.block i).1 : ℝ) /
        (S.core.parameters.H N (C.block i).1 : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using
      S.core.parameters.Xdom (C.block i).1 1 (by norm_num)
  filter_upwards [hratio.eventually_gt_atTop 1] with N hratioN
  have hHpos : 0 < (S.core.parameters.H N (C.block i).1 : ℝ) := by
    exact_mod_cast S.core.parameters.Hpos N (C.block i).1
  have hHle : (S.core.parameters.H N (C.block i).1 : ℝ) <
      Real.log (S.core.parameters.X N (C.block i).1 : ℝ) :=
    by simpa using (lt_div_iff₀ hHpos).mp hratioN
  have hHone : 1 ≤ (S.core.parameters.H N (C.block i).1 : ℝ) := by
    exact_mod_cast (Nat.one_le_of_lt
      (S.core.parameters.Hpos N (C.block i).1))
  have hXpos : 0 < (S.core.parameters.X N (C.block i).1 : ℝ) := by
    exact_mod_cast S.core.parameters.Xpos N (C.block i).1
  have hcut := S.gapStage.valid_raw_cutoffs N (C.block i).1
  have hfrac : (primorial (N + 1) : ℝ) /
      S.core.parameters.X N (C.block i).1 ≤ 1 / 4 := by
    apply (div_le_iff₀ hXpos).2
    have hcutR : 4 * (primorial (N + 1) : ℝ) ≤
        (S.core.parameters.X N (C.block i).1 : ℝ) := by exact_mod_cast hcut
    nlinarith
  linarith

theorem rawPivot_dominates_samplingInput {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l i : Fin n) (hli : l < i) (r : ℕ) :
    OAI.MicrocellScale.Dominates
      (fun N => (A.X N i : ℝ))
      (fun N => (2 + primorial (N + 1) + (masterScaleV A N l) ^ r +
        1 + masterScaleV A N l : ℝ)) := by
  intro B hB
  have hlog := logPivot_dominates_samplingInput A l i hli r B hB
  apply tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards with N
  have hXpos : 0 ≤ (A.X N i : ℝ) := by positivity
  exact div_le_div_of_nonneg_right
    (Real.log_le_self hXpos) (by positivity)

noncomputable def pivotBaseResidueErrorSum {K s m r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) : ℝ :=
  ∑ i : Fin m,
    harmonicResidueUniformError (S.core.parameters.X N (C.block i).1)
      (primorial (N + 1)) (masterScaleV S.core.parameters N C.gap ^ r)

theorem pivotBaseResidueErrorSum_superPolynomialSmall
    {K s m r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) :
    SuperPolynomialSmall (pivotBaseResidueErrorSum (r := r) S C)
      (fun N => (masterScaleV S.core.parameters N C.gap : ℝ)) := by
  intro B hB
  let Vseq : ℕ → ℕ := fun N => masterScaleV S.core.parameters N C.gap
  have hsample (i : Fin m) :
      SuperPolynomialSmall
        (fun N => harmonicResidueUniformError
          (S.core.parameters.X N (C.block i).1) (primorial (N + 1)) (Vseq N ^ r))
        (fun N => (Vseq N : ℝ)) := by
    let Wseq : ℕ → ℕ := fun N => primorial (N + 1)
    let Kseq : ℕ → ℕ := fun N => Vseq N ^ r
    let Hseq : ℕ → ℕ := fun _ => 1
    let Xseq : ℕ → ℕ := fun N => S.core.parameters.X N (C.block i).1
    have hK : ∀ N, 1 ≤ Kseq N := by
      intro N
      dsimp [Kseq, Vseq]
      have hV : 2 ≤ masterScaleV S.core.parameters N C.gap := by
        unfold masterScaleV
        omega
      exact Nat.one_le_pow r _ (by omega : 0 < masterScaleV S.core.parameters N C.gap)
    have hH : ∀ N, 1 ≤ Hseq N := by intro N; simp [Hseq]
    have hV : ∀ N, 1 ≤ Vseq N := by
      intro N
      dsimp [Vseq]
      have hV : 2 ≤ masterScaleV S.core.parameters N C.gap := by
        unfold masterScaleV
        omega
      omega
    have hW : ∀ N, Wseq N = primorial (N + 1) := by intro N; rfl
    have hX : ∀ᶠ N in atTop, 2 ≤ Xseq N := by
      filter_upwards [Filter.Eventually.of_forall
        (fun N => S.gapStage.valid_raw_cutoffs N (C.block i).1)] with N hcut
      dsimp [Xseq]
      have hW : 0 < primorial (N + 1) := primorial_pos (N + 1)
      omega
    have hden : ∀ᶠ N in atTop,
        Real.log (Xseq N : ℝ) > (Wseq N : ℝ) / Xseq N := by
      simpa [Wseq, Xseq] using
        pivot_sampling_log_condition_eventually S C i
    have hDomX : OAI.MicrocellScale.Dominates
        (fun N => (Xseq N : ℝ))
        (fun N => 2 + (Wseq N : ℝ) + (Kseq N : ℝ) +
          (Hseq N : ℝ) + (Vseq N : ℝ)) := by
      simpa [Wseq, Kseq, Hseq, Vseq] using
        rawPivot_dominates_samplingInput S.core.parameters C.gap (C.block i).1
          (C.pivots_after_gap i) r
    have hDomLogX : OAI.MicrocellScale.Dominates
        (fun N => Real.log (Xseq N : ℝ))
        (fun N => 2 + (Wseq N : ℝ) + (Kseq N : ℝ) + (Vseq N : ℝ)) := by
      intro D hD
      have hfull := logPivot_dominates_samplingInput S.core.parameters C.gap
        (C.block i).1 (C.pivots_after_gap i) r D hD
      apply tendsto_atTop_mono' atTop ?_ hfull
      filter_upwards with N
      have hlogNonneg : 0 ≤ Real.log (Xseq N : ℝ) := by
        have hXpos : 0 < Xseq N := S.core.parameters.Xpos N (C.block i).1
        exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt hXpos))
      have hsmall :
          (2 + (Wseq N : ℝ) + (Kseq N : ℝ) + (Vseq N : ℝ)) ≤
            (2 + (Wseq N : ℝ) + (Kseq N : ℝ) + 1 + (Vseq N : ℝ)) := by
        dsimp [Wseq, Kseq, Vseq]
        linarith
      exact div_le_div_of_nonneg_left hlogNonneg
        (Real.rpow_pos_of_pos (by positivity) D)
        (Real.rpow_le_rpow (by positivity)
          (by simpa [Wseq, Kseq, Vseq] using hsmall) hD.le)
    have hasym := FromArithmetic.sampling_asymptotics
      Wseq Kseq Hseq Vseq Xseq hK hH hV hW hX hden hDomX hDomLogX
    exact hasym.1
  have hterm (i : Fin m) : Tendsto
      (fun N => harmonicResidueUniformError
        (S.core.parameters.X N (C.block i).1) (primorial (N + 1))
        (masterScaleV S.core.parameters N C.gap ^ r) *
          (masterScaleV S.core.parameters N C.gap : ℝ) ^ B) atTop (nhds 0) := by
    simpa [Vseq] using hsample i B hB
  have hsum (s : Finset (Fin m)) : Tendsto
      (fun N => ∑ i ∈ s,
        harmonicResidueUniformError
          (S.core.parameters.X N (C.block i).1) (primorial (N + 1))
          (masterScaleV S.core.parameters N C.gap ^ r) *
            (masterScaleV S.core.parameters N C.gap : ℝ) ^ B) atTop
      (nhds (∑ i ∈ s, (0 : ℝ))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using (hterm i).add ih
  have hsumUniv : Tendsto
      (fun N => ∑ i : Fin m,
        harmonicResidueUniformError
          (S.core.parameters.X N (C.block i).1) (primorial (N + 1))
          (masterScaleV S.core.parameters N C.gap ^ r) *
            (masterScaleV S.core.parameters N C.gap : ℝ) ^ B) atTop (nhds 0) := by
    simpa using hsum Finset.univ
  have hsumError : Tendsto
      (fun N => pivotBaseResidueErrorSum (r := r) S C N *
        (masterScaleV S.core.parameters N C.gap : ℝ) ^ B) atTop (nhds 0) := by
    convert hsumUniv using 1
    funext N
    simp [pivotBaseResidueErrorSum, Finset.sum_mul]
  simpa [Vseq] using hsumError

theorem pivotBaseResidueLaw_finiteL1_le_sum_sampling_errors
    {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N modulus : ℕ)
    (hmodulus : 0 < modulus) (hcop : Nat.Coprime modulus (primorial (N + 1)))
    (hX : ∀ i, 2 ≤ S.core.parameters.X N (C.block i).1)
    (hlog : ∀ i, Real.log (S.core.parameters.X N (C.block i).1 : ℝ) >
      (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1) :
    finiteL1 (FromArithmetic.baseResidueLaw modulus hmodulus
      (pivotMass S.core.parameters C N)) (uniformBaseResidueLaw modulus m) ≤
      ∑ i : Fin m,
        harmonicResidueError (S.core.parameters.X N (C.block i).1)
          (primorial (N + 1)) modulus := by
  classical
  let W := primorial (N + 1)
  let μ : Fin m → Fin modulus → ℝ := fun i a =>
    harmonicResidueLaw
      (harmonicLaw (S.core.parameters.X N (C.block i).1) W) modulus a
  let ν : Fin m → Fin modulus → ℝ := fun _ a => uniformResidueLaw modulus a
  have hbase (r : Fin m → Fin modulus) :
      FromArithmetic.baseResidueLaw modulus hmodulus
        (pivotMass S.core.parameters C N) r = ∏ i, μ i (r i) := by
    rw [pivotBaseResidueLaw_eq_prod_harmonicResidueLaw]
  have huniform (r : Fin m → Fin modulus) :
      uniformBaseResidueLaw modulus m r = ∏ i, ν i (r i) := by
    simp [uniformBaseResidueLaw, uniformResidueLaw, ν, Finset.prod_const]
  have hnorm (i : Fin m) :
      0 < harmonicNormalizer (S.core.parameters.X N (C.block i).1) W :=
    harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block i).1)
  have hmassAbs (i : Fin m) : ∑ a : Fin modulus, |μ i a| = 1 := by
    have hnonneg (a : Fin modulus) : 0 ≤ μ i a := by
      exact harmonicResidueLaw_nonneg _ _ _ (hnorm i) a
    calc
      (∑ a : Fin modulus, |μ i a|) = ∑ a : Fin modulus, μ i a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [abs_of_nonneg (hnonneg a)]
      _ = 1 := harmonicResidueLaw_sum_one _ _ _ hmodulus
        (S.core.parameters.Xpos N (C.block i).1) (hnorm i)
  have hnuAbs : ∑ a : Fin modulus, |uniformResidueLaw modulus a| = 1 := by
    have hmodR : (0 : ℝ) < modulus := by exact_mod_cast hmodulus
    calc
      (∑ a : Fin modulus, |uniformResidueLaw modulus a|) =
          ∑ a : Fin modulus, 1 / (modulus : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [uniformResidueLaw, abs_of_pos (one_div_pos.mpr hmodR)]
      _ = 1 := by simp [Finset.sum_const, div_eq_mul_inv, hmodR.ne']
  have herr (i : Fin m) :
      finiteL1 (μ i) (ν i) ≤
        harmonicResidueError (S.core.parameters.X N (C.block i).1) W modulus := by
    have hsample := FromArithmetic.sampling_pointwise_claim
      (S.core.parameters.X N (C.block i).1) W (primorial_pos (N + 1))
      (hX i) (hlog i)
    exact hsample.residue_total_mass (hX i) (hlog i) modulus hcop hmodulus
  have htensor := FromArithmetic.finite_product_l1_telescoping μ ν
  have hfactor (i : Fin m) :
      ∏ j ∈ Finset.univ.erase i,
        max (∑ a : Fin modulus, |μ j a|) (∑ a : Fin modulus, |ν j a|) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [hmassAbs j, hnuAbs]
    simp
  have hL1eq :
      finiteL1 (FromArithmetic.baseResidueLaw modulus hmodulus
        (pivotMass S.core.parameters C N)) (uniformBaseResidueLaw modulus m) =
        finiteL1 (fun r : Fin m → Fin modulus => ∏ i, μ i (r i))
          (fun r => ∏ i, ν i (r i)) := by
    unfold finiteL1
    apply Finset.sum_congr rfl
    intro r hr
    rw [hbase r, huniform r]
  calc
    finiteL1 (FromArithmetic.baseResidueLaw modulus hmodulus
      (pivotMass S.core.parameters C N)) (uniformBaseResidueLaw modulus m) =
        finiteL1 (fun r : Fin m → Fin modulus => ∏ i, μ i (r i))
          (fun r => ∏ i, ν i (r i)) := hL1eq
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) := by
      calc
        _ ≤ ∑ i, finiteL1 (μ i) (ν i) *
            ∏ j ∈ Finset.univ.erase i,
              max (∑ a : Fin modulus, |μ j a|) (∑ a : Fin modulus, |ν j a|) := htensor
        _ = ∑ i, finiteL1 (μ i) (ν i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hfactor i]
          ring
    _ ≤ ∑ i : Fin m,
        harmonicResidueError (S.core.parameters.X N (C.block i).1) W modulus :=
      Finset.sum_le_sum fun i hi => herr i


noncomputable def maskRowDivisorTemplate {K m q r : ℕ}
    (C : MasterChain K m) (Sh : RowShape m q r) (R : Fin r) :
    DivisorTemplate K K := by
  classical
  let T : Finset (Fin K) := (C.block (Sh.row R).anchor).2.val
  have hT : T.card ≤ K := by
    calc
      T.card ≤ Fintype.card (Fin K) := Finset.card_le_univ T
      _ = K := by simp
  exact divisorTemplateOfFinset T hT

noncomputable def maskEmptyDivisorTemplate {K : ℕ} : DivisorTemplate K K :=
  divisorTemplateOfFinset (∅ : Finset (Fin K)) (by simp)

theorem independentPrimePoolSupport_mem_iff {q : ℕ} (lo hi : Fin q → ℕ)
    (p : Fin q → ℕ) :
    p ∈ independentPrimePoolSupport lo hi ↔
      ∀ i, p i ∈ primePoolSupport (lo i) (hi i) := by
  unfold independentPrimePoolSupport
  exact Fintype.mem_piFinset

def MaskRowAnchorReady {K s m q r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (N : ℕ) : Prop :=
  ∀ p, p ∈ independentPrimePoolSupport
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) →
    ∀ v (hv : v.Prime), N + 1 < v → v ≤ masterScaleV S.core.parameters N C.gap →
    ∀ R, FromArithmetic.rationalResidue v hv
      (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N)
        N p R (Sh.row R).anchor) ≠ 0

def MaskRowPairwiseReady {K s m q r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (N : ℕ) : Prop :=
  ∀ p, p ∈ independentPrimePoolSupport
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) →
    ∀ v (hv : v.Prime), N + 1 < v → v ≤ masterScaleV S.core.parameters N C.gap →
    (∀ Q ∈ Dm, ¬ ((v : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
    ∀ R I, R ≠ I →
      ∃ j k,
        FromArithmetic.rationalResidue v hv
            (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N)
              N p R j) *
          FromArithmetic.rationalResidue v hv
            (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N)
              N p I k) ≠
        FromArithmetic.rationalResidue v hv
            (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N)
              N p R k) *
          FromArithmetic.rationalResidue v hv
          (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N)
              N p I j)

def MaskRowDataGoodDomain {K s m q r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (N : ℕ) (p : Fin s → ℕ) : Prop :=
  (∀ i : Fin m, Real.log (S.core.parameters.X N (C.block i).1 : ℝ) >
      (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1) ∧
  (∀ (R : Fin r) (p' : Fin s → ℕ) (x : Fin m → ℤ),
      (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
      (fun j => p' (ι j)) (fun j => (x j : ℚ))).den = 1) ∧
  (∀ (R : Fin r) (j : Fin m), (rowShapeLinearCoefficients Sh ι
      (chainScale S.core.parameters C a N) N p R j).den = 1) ∧
  MaskRowAnchorReady S C a Sh ι N ∧ MaskRowPairwiseReady S C a Sh ι N ∧
  p ∈ independentPrimePoolSupport
    (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) ∧
  ∀ j, masterScaleV S.core.parameters N C.gap < p j

theorem maskRowAnchorReady_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) :
    ∀ᶠ N in atTop, MaskRowAnchorReady S C a Sh ι N := by
  filter_upwards [rowShapeLinearCoefficients_anchor_residue_ne_zero_eventually
      S C a ha Sh ι] with N hready
  intro p hp v hv hNv hvV R
  apply hready p R v hv hNv hvV
  intro i
  have hi := (independentPrimePoolSupport_mem_iff
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) p).mp hp i
  rcases Finset.mem_filter.mp hi with ⟨hIco, hprime⟩
  rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
  exact ⟨hlo, hhi, hprime⟩

theorem maskRowPairwiseReady_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm) :
    ∀ᶠ N in atTop, MaskRowPairwiseReady S C a Sh ι N := by
  filter_upwards [rowShapeLinearCoefficients_pairwise_independent_eventually
      S C a ha Sh ι hlisted] with N hready
  intro p hp v hv hNv hvV havoid R I hRI
  have hpool : ∀ i,
      (S.primeStage.pool N C.gap).lower ≤ p i ∧
        p i < (S.primeStage.pool N C.gap).upper ∧ (p i).Prime := by
    intro i
    have hi := (independentPrimePoolSupport_mem_iff
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) p).mp hp i
    rcases Finset.mem_filter.mp hi with ⟨hIco, hprime⟩
    rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
    exact ⟨hlo, hhi, hprime⟩
  obtain ⟨j, k, hne⟩ := hready p hpool v hv hNv hvV havoid R I hRI
  exact ⟨j, k, sub_ne_zero.mp hne⟩

theorem maskRowDataGoodDomain_eventually {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm) :
    ∀ᶠ N in atTop, ∀ p,
      p ∈ independentPrimePoolSupport
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) →
      MaskRowDataGoodDomain S C a Sh ι N p := by
  have hlogs : ∀ᶠ N in atTop, ∀ i : Fin m,
      Real.log (S.core.parameters.X N (C.block i).1 : ℝ) >
        (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1 :=
    Filter.eventually_all.2 fun i => pivot_sampling_log_condition_eventually S C i
  have hrowden := rowForm_den_one_eventually (q := q) S C a ha
  have hcoeffden := rowShapeLinearCoefficients_den_one_eventually S C a ha Sh ι
  have hanchor := maskRowAnchorReady_eventually S C a ha Sh ι
  have hpair := maskRowPairwiseReady_eventually S C a ha Sh ι hlisted
  have hpool := pool_lower_gt_masterScaleV_eventually S C.gap
  filter_upwards [hlogs, hrowden, hcoeffden, hanchor, hpair, hpool]
    with N hlogs hrowden hcoeffden hanchor hpair hpool
  intro p hp
  refine ⟨?_, ?_, ?_, hanchor, hpair, hp, ?_⟩
  · exact hlogs
  · intro R p' x
    exact hrowden (Sh.row R) (fun j => p' (ι j)) x
  · intro R j
    exact hcoeffden p R j
  · intro j
    have hj := (independentPrimePoolSupport_mem_iff
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) p).mp hp j
    rcases Finset.mem_filter.mp hj with ⟨hIco, hprime⟩
    rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
    exact lt_of_lt_of_le hpool hlo

theorem maskWeightedLinearFormsData_goodDomain_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm) :
    ∀ᶠ N in atTop, ∀ p,
      p ∈ independentPrimePoolSupport
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) →
      MaskRowDataGoodDomain S C a Sh ι N p :=
  maskRowDataGoodDomain_eventually S C a ha Sh ι hlisted

def masterCRTOptionFactor (w e V : ℕ) : Option (CRTPrimeRange w V) → ℕ
  | none => primorial w ^ e
  | some p => p.val

theorem masterCRTModulus_eq_option_prod (w e V : ℕ) :
    masterCRTModulus w e V =
      ∏ o : Option (CRTPrimeRange w V), masterCRTOptionFactor w e V o := by
  classical
  have hattach :
      (∏ p : CRTPrimeRange w V, p.val) =
        ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p := by
    simpa [CRTPrimeRange] using
      (Finset.prod_attach ((Finset.Ioc w (V + 1)).filter Nat.Prime) (fun p => p))
  unfold masterCRTModulus
  rw [← hattach]
  simp [masterCRTOptionFactor, Fintype.prod_option]

theorem masterCRTOptionFactor_none_coprime {w e V : ℕ}
    (p : CRTPrimeRange w V) :
    Nat.Coprime (masterCRTOptionFactor w e V none)
      (masterCRTOptionFactor w e V (some p)) := by
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hpw : w < p.val :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.property).1).1
  have hnot : ¬ p.val ∣ primorial w := by
    intro hdiv
    have hle := hp.dvd_primorial_iff.mp hdiv
    omega
  have hnotPow : ¬ p.val ∣ (primorial w) ^ e := by
    intro hdiv
    exact hnot (hp.dvd_of_dvd_pow hdiv)
  have hcop : Nat.Coprime p.val ((primorial w) ^ e) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hnotPow
  simpa [masterCRTOptionFactor] using hcop.symm

theorem masterCRTOptionFactor_pairwise_coprime (w e V : ℕ) :
    Pairwise (fun a b => Nat.Coprime (masterCRTOptionFactor w e V a)
      (masterCRTOptionFactor w e V b)) := by
  classical
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some p => exact masterCRTOptionFactor_none_coprime p
  | some p =>
      cases b with
      | none => exact (masterCRTOptionFactor_none_coprime p).symm
      | some q =>
          have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
          have hq : q.val.Prime := (Finset.mem_filter.mp q.property).2
          have hpq : p.val ≠ q.val := by
            intro heq
            apply hab
            have hsub : p = q := Subtype.ext heq
            rw [hsub]
          have hcop : Nat.Coprime p.val q.val := by
            apply (Nat.Prime.coprime_iff_not_dvd hp).2
            intro hdvd
            exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
          simpa [masterCRTOptionFactor] using hcop

theorem zmod_finEquiv_val {Q : ℕ} [NeZero Q] (a : Fin Q) :
    (ZMod.finEquiv Q a).val = a.val := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne Q)
  rfl

theorem zmod_finEquiv_eq_natCast {Q : ℕ} [NeZero Q] (a : Fin Q) :
    ZMod.finEquiv Q a = (a.val : ZMod Q) := by
  apply ZMod.val_injective Q
  rw [zmod_finEquiv_val, ZMod.val_natCast]
  exact (Nat.mod_eq_of_lt a.isLt).symm

theorem zmod_finEquiv_symm_val {Q : ℕ} [NeZero Q] (a : ZMod Q) :
    ((ZMod.finEquiv Q).symm a).val = a.val := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne Q)
  rfl

noncomputable def masterCRTDecompositionEquiv (w e V : ℕ) :
    ZMod (masterCRTModulus w e V) ≃+*
      ZMod (primorial w ^ e) × (∀ p : CRTPrimeRange w V, ZMod p.val) := by
  classical
  let f := masterCRTOptionFactor w e V
  have hprod := masterCRTModulus_eq_option_prod w e V
  have eProduct : ZMod (masterCRTModulus w e V) ≃+*
      (∀ o : Option (CRTPrimeRange w V), ZMod (f o)) := by
    exact (ZMod.ringEquivCongr hprod).trans
      (ZMod.prodEquivPi f (masterCRTOptionFactor_pairwise_coprime w e V))
  let eOption : (∀ o : Option (CRTPrimeRange w V), ZMod (f o)) ≃+*
      ZMod (f none) × (∀ p : CRTPrimeRange w V, ZMod (f (some p))) :=
    RingEquiv.piOptionEquivProd
  exact eProduct.trans eOption

noncomputable def masterCRTFinResidueEquiv (w e V : ℕ) :
    Fin (masterCRTModulus w e V) ≃ Fin (primorial w ^ e) × CRTResidues w V := by
  classical
  have hQ : 0 < masterCRTModulus w e V := by
    unfold masterCRTModulus
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp hp).2.pos
  letI : NeZero (masterCRTModulus w e V) := ⟨hQ.ne'⟩
  have hsmall : 0 < primorial w ^ e := pow_pos (primorial_pos w) e
  haveI : NeZero (primorial w ^ e) := ⟨hsmall.ne'⟩
  have eSmall : ZMod (primorial w ^ e) ≃ Fin (primorial w ^ e) :=
    (ZMod.finEquiv (primorial w ^ e)).symm.toEquiv
  have eFin (p : CRTPrimeRange w V) : ZMod p.val ≃ Fin p.val := by
    have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
    letI : NeZero p.val := ⟨hp.pos.ne'⟩
    exact (ZMod.finEquiv p.val).symm.toEquiv
  have ePi : (∀ p : CRTPrimeRange w V, ZMod p.val) ≃
      (∀ p : CRTPrimeRange w V, Fin p.val) :=
    Equiv.piCongrRight (fun p : CRTPrimeRange w V => eFin p)
  exact (ZMod.finEquiv (masterCRTModulus w e V)).toEquiv.trans <|
    (masterCRTDecompositionEquiv w e V).toEquiv.trans <|
      Equiv.prodCongr eSmall ePi

theorem masterCRTFinResidueEquiv_snd (w e V : ℕ)
    (a : Fin (masterCRTModulus w e V)) :
    (masterCRTFinResidueEquiv w e V a).2 = integerCRTResidues w V a.val := by
  classical
  have hQ : 0 < masterCRTModulus w e V := by
    unfold masterCRTModulus
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp hp).2.pos
  letI : NeZero (masterCRTModulus w e V) := ⟨hQ.ne'⟩
  have hsmall : 0 < primorial w ^ e := pow_pos (primorial_pos w) e
  letI : NeZero (primorial w ^ e) := ⟨hsmall.ne'⟩
  have hprod := masterCRTModulus_eq_option_prod w e V
  letI : NeZero (∏ o : Option (CRTPrimeRange w V), masterCRTOptionFactor w e V o) := by
    refine ⟨?_⟩
    rw [← hprod]
    exact hQ.ne'
  have hproj (p : CRTPrimeRange w V) :
      (masterCRTDecompositionEquiv w e V
        ((ZMod.finEquiv (masterCRTModulus w e V)) a)).2 p =
        (a.val % p.val : ZMod p.val) := by
    have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
    letI : NeZero p.val := ⟨hp.pos.ne'⟩
    change (ZMod.prodEquivPi (masterCRTOptionFactor w e V)
        (masterCRTOptionFactor_pairwise_coprime w e V)
        ((ZMod.ringEquivCongr (masterCRTModulus_eq_option_prod w e V))
          ((ZMod.finEquiv (masterCRTModulus w e V)) a)) (some p)) = _
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply]
    rw [ZMod.cast_eq_val, ZMod.ringEquivCongr_val]
    rw [zmod_finEquiv_val]
    simp [masterCRTOptionFactor]
    rfl
  funext p
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  letI : NeZero p.val := ⟨hp.pos.ne'⟩
  apply Fin.ext
  change ((ZMod.finEquiv p.val).symm
      ((masterCRTDecompositionEquiv w e V
        ((ZMod.finEquiv (masterCRTModulus w e V)) a)).2 p)).val = a.val % p.val
  rw [zmod_finEquiv_symm_val]
  have hval := congrArg ZMod.val (hproj p)
  simpa [integerCRTResidues] using hval

theorem masterCRTFinResidueEquiv_coprime_iff {w e V : ℕ}
    (a : Fin (masterCRTModulus w e V)) :
    Nat.Coprime a.val (masterCRTModulus w e V) ↔
      Nat.Coprime (masterCRTFinResidueEquiv w e V a).1.val (primorial w ^ e) ∧
        ∀ p : CRTPrimeRange w V,
          Nat.Coprime ((masterCRTFinResidueEquiv w e V a).2 p).val p.val := by
  classical
  have hQ : 0 < masterCRTModulus w e V := by
    unfold masterCRTModulus
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp hp).2.pos
  letI : NeZero (masterCRTModulus w e V) := ⟨hQ.ne'⟩
  have hsmall : 0 < primorial w ^ e := pow_pos (primorial_pos w) e
  letI : NeZero (primorial w ^ e) := ⟨hsmall.ne'⟩
  let E := masterCRTFinResidueEquiv w e V
  let zprod := masterCRTDecompositionEquiv w e V
      ((ZMod.finEquiv (masterCRTModulus w e V)) a)
  have hsmallEq :
      ZMod.finEquiv (primorial w ^ e) (E a).1 =
        zprod.1 := by
    change ZMod.finEquiv (primorial w ^ e)
      ((ZMod.finEquiv (primorial w ^ e)).symm zprod.1) = zprod.1
    exact (ZMod.finEquiv (primorial w ^ e)).apply_symm_apply zprod.1
  have hbigVal (p : CRTPrimeRange w V) :
      (zprod.2 p).val = ((E a).2 p).val := by
    have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
    letI : NeZero p.val := ⟨hp.pos.ne'⟩
    change (zprod.2 p).val = ((ZMod.finEquiv p.val).symm (zprod.2 p)).val
    exact (zmod_finEquiv_symm_val (zprod.2 p)).symm
  have hsource : Nat.Coprime a.val (masterCRTModulus w e V) ↔
      IsUnit (ZMod.finEquiv (masterCRTModulus w e V) a) := by
    rw [zmod_finEquiv_eq_natCast]
    exact (ZMod.isUnit_iff_coprime a.val (masterCRTModulus w e V)).symm
  have hRing : IsUnit (ZMod.finEquiv (masterCRTModulus w e V) a) ↔
      IsUnit zprod := by
    constructor
    · intro h
      exact h.map (masterCRTDecompositionEquiv w e V).toRingHom
    · intro h
      simpa [zprod] using h.map (masterCRTDecompositionEquiv w e V).symm.toRingHom
  have hsmallUnit : IsUnit
      zprod.1 ↔
      Nat.Coprime (E a).1.val (primorial w ^ e) := by
    rw [← hsmallEq]
    rw [zmod_finEquiv_eq_natCast]
    exact ZMod.isUnit_iff_coprime ((E a).1).val (primorial w ^ e)
  have hbigUnit (p : CRTPrimeRange w V) :
      IsUnit (zprod.2 p) ↔
        Nat.Coprime ((E a).2 p).val p.val := by
    have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
    letI : NeZero p.val := ⟨hp.pos.ne'⟩
    have hcast : zprod.2 p = (((E a).2 p).val : ZMod p.val) := by
      apply ZMod.val_injective p.val
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt ((E a).2 p).isLt]
      exact hbigVal p
    rw [hcast]
    exact ZMod.isUnit_iff_coprime ((E a).2 p).val p.val
  calc
    Nat.Coprime a.val (masterCRTModulus w e V) ↔
        IsUnit (ZMod.finEquiv (masterCRTModulus w e V) a) := hsource
    _ ↔ IsUnit (masterCRTDecompositionEquiv w e V
        (ZMod.finEquiv (masterCRTModulus w e V) a)) := hRing
    _ ↔ Nat.Coprime (E a).1.val (primorial w ^ e) ∧
        ∀ p : CRTPrimeRange w V, Nat.Coprime ((E a).2 p).val p.val := by
      rw [Prod.isUnit_iff, Pi.isUnit_iff]
      constructor
      · rintro ⟨hs, hp⟩
        exact ⟨hsmallUnit.mp hs, fun p => (hbigUnit p).mp (hp p)⟩
      · rintro ⟨hs, hp⟩
        exact ⟨hsmallUnit.mpr hs, fun p => (hbigUnit p).mpr (hp p)⟩

theorem finCoprimeIndicator_sum_eq_totient (n : ℕ) :
    (∑ a : Fin n, if Nat.Coprime a.val n then (1 : ℝ) else 0) =
      (Nat.totient n : ℝ) := by
  classical
  let e : {a : Fin n // Nat.Coprime a.val n} ≃
      {a : ℕ // a < n ∧ Nat.Coprime n a} := {
    toFun := fun (a : {a : Fin n // Nat.Coprime a.val n}) =>
      (⟨a.val.val, And.intro a.val.isLt a.property.symm⟩ :
        {a : ℕ // a < n ∧ Nat.Coprime n a})
    invFun := fun (a : {a : ℕ // a < n ∧ Nat.Coprime n a}) =>
      (⟨⟨a.val, a.property.1⟩, a.property.2.symm⟩ :
        {a : Fin n // Nat.Coprime a.val n})
    left_inv := fun a => by
      apply Subtype.ext
      apply Fin.ext
      rfl
    right_inv := fun a => by
      apply Subtype.ext
      rfl
  }
  have hcard : Fintype.card {a : Fin n // Nat.Coprime a.val n} = Nat.totient n := by
    calc
      Fintype.card {a : Fin n // Nat.Coprime a.val n} =
          Nat.card {a : Fin n // Nat.Coprime a.val n} := Nat.card_eq_fintype_card.symm
      _ = Nat.card {a : ℕ // a < n ∧ Nat.Coprime n a} := Nat.card_congr e
      _ = Nat.totient n := (Nat.totient_eq_card_lt_and_coprime n).symm
  calc
    (∑ a : Fin n, if Nat.Coprime a.val n then (1 : ℝ) else 0) =
        (Fintype.card {a : Fin n // Nat.Coprime a.val n} : ℝ) := by
          rw [Finset.sum_boole]
          simp [Fintype.card_subtype]
    _ = (Nat.totient n : ℝ) := by exact_mod_cast hcard

theorem masterCRTModulus_totient (w e V : ℕ) :
    Nat.totient (masterCRTModulus w e V) =
      Nat.totient (primorial w ^ e) *
        ∏ p : CRTPrimeRange w V, (p.val - 1) := by
  classical
  have hQ : 0 < masterCRTModulus w e V := by
    unfold masterCRTModulus
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp hp).2.pos
  have hsmall : 0 < primorial w ^ e := pow_pos (primorial_pos w) e
  letI : NeZero (masterCRTModulus w e V) := ⟨hQ.ne'⟩
  letI : NeZero (primorial w ^ e) := ⟨hsmall.ne'⟩
  letI : ∀ p : CRTPrimeRange w V, NeZero p.val := fun p =>
    ⟨((Finset.mem_filter.mp p.property).2).pos.ne'⟩
  let hRing := masterCRTDecompositionEquiv w e V
  have hcard : Fintype.card (Units (ZMod (masterCRTModulus w e V))) =
      Fintype.card (Units (ZMod (primorial w ^ e))) *
        ∏ p : CRTPrimeRange w V, Fintype.card (Units (ZMod p.val)) := by
    calc
      Fintype.card (Units (ZMod (masterCRTModulus w e V))) =
          Fintype.card (Units
            (ZMod (primorial w ^ e) × (∀ p : CRTPrimeRange w V, ZMod p.val))) :=
          Fintype.card_congr (Units.mapEquiv hRing).toEquiv
      _ = Fintype.card (Units (ZMod (primorial w ^ e))) *
          Fintype.card (Units (∀ p : CRTPrimeRange w V, ZMod p.val)) := by
            rw [Fintype.card_congr (MulEquiv.prodUnits).toEquiv, Fintype.card_prod]
      _ = Fintype.card (Units (ZMod (primorial w ^ e))) *
          ∏ p : CRTPrimeRange w V, Fintype.card (Units (ZMod p.val)) := by
            congr 1
            rw [Fintype.card_congr (MulEquiv.piUnits).toEquiv, Fintype.card_pi]
  have hcardTotient : Nat.totient (masterCRTModulus w e V) =
      Nat.totient (primorial w ^ e) *
        ∏ p : CRTPrimeRange w V, Nat.totient p.val := by
    simpa only [ZMod.card_units_eq_totient] using hcard
  calc
    Nat.totient (masterCRTModulus w e V) =
        Nat.totient (primorial w ^ e) *
          ∏ p : CRTPrimeRange w V, Nat.totient p.val := hcardTotient
    _ = Nat.totient (primorial w ^ e) *
          ∏ p : CRTPrimeRange w V, (p.val - 1) := by
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        exact Nat.totient_prime ((Finset.mem_filter.mp p.property).2)

def finitePushforwardLaw {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (y : β) : ℝ :=
  ∑ x, μ x * if f x = y then 1 else 0

noncomputable def uniformCRTResidueLaw {w V : ℕ} (r : CRTResidues w V) : ℝ :=
  ∏ p : CRTPrimeRange w V,
    if Nat.Coprime (r p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0

theorem uniformUnitResidueLaw_pushforward {w e V : ℕ}
    (r : CRTResidues w V) :
    finitePushforwardLaw
      (fun a : Fin (masterCRTModulus w e V) => integerCRTResidues w V a.val)
      (uniformUnitResidueLaw (masterCRTModulus w e V)) r =
        uniformCRTResidueLaw r := by
  classical
  let Q := masterCRTModulus w e V
  let n := primorial w ^ e
  have hQ : 0 < Q := by
    dsimp [Q]
    unfold masterCRTModulus
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp hp).2.pos
  have hn : 0 < n := by dsimp [n]; exact pow_pos (primorial_pos w) e
  letI : NeZero Q := ⟨hQ.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  letI : ∀ p : CRTPrimeRange w V, NeZero p.val := fun p =>
    ⟨((Finset.mem_filter.mp p.property).2).pos.ne'⟩
  let E := masterCRTFinResidueEquiv w e V
  let g : Fin Q → ℝ := fun a =>
    uniformUnitResidueLaw Q a *
      (if integerCRTResidues w V a.val = r then 1 else 0)
  have hterm (z : Fin n × CRTResidues w V) :
      g (E.symm z) =
        (if Nat.Coprime z.1.val n ∧
            ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val
          then 1 / (Nat.totient Q : ℝ) else 0) *
          (if z.2 = r then 1 else 0) := by
    dsimp [g, uniformUnitResidueLaw, E]
    have hcop := masterCRTFinResidueEquiv_coprime_iff (w := w) (e := e)
      (V := V) ((masterCRTFinResidueEquiv w e V).symm z)
    have hproj := masterCRTFinResidueEquiv_snd w e V
      ((masterCRTFinResidueEquiv w e V).symm z)
    have hE : masterCRTFinResidueEquiv w e V
        ((masterCRTFinResidueEquiv w e V).symm z) = z :=
      (masterCRTFinResidueEquiv w e V).apply_symm_apply z
    have hcop' : Nat.Coprime
        ((masterCRTFinResidueEquiv w e V).symm z).val Q ↔
          Nat.Coprime z.1.val n ∧
            ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val := by
      simpa [hE] using hcop
    have hres : integerCRTResidues w V
        ((masterCRTFinResidueEquiv w e V).symm z).val = z.2 := by
      rw [← hproj]
      exact congrArg Prod.snd hE
    by_cases hc : Nat.Coprime
        ((masterCRTFinResidueEquiv w e V).symm z).val Q
    · have hc' := hcop'.mp hc
      have ht : Nat.Coprime z.1.val n ∧
          ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val := hc'
      simp only [if_pos hc, if_pos ht]
      rw [hres]
    · have hc' : ¬ (Nat.Coprime z.1.val n ∧
          ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val) := by
        intro h
        exact hc (hcop'.mpr h)
      simp only [if_neg hc, if_neg hc', zero_mul]
  have hsum :
      finitePushforwardLaw
        (fun a : Fin Q => integerCRTResidues w V a.val)
        (uniformUnitResidueLaw Q) r =
      ∑ z : Fin n × CRTResidues w V,
        (if Nat.Coprime z.1.val n ∧
            ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val
          then 1 / (Nat.totient Q : ℝ) else 0) *
          (if z.2 = r then 1 else 0) := by
    unfold finitePushforwardLaw
    change (∑ a : Fin Q, g a) = _
    rw [← Equiv.sum_comp E.symm g]
    apply Finset.sum_congr rfl
    intro z hz
    exact hterm z
  have hpair :
      (∑ z : Fin n × CRTResidues w V,
        (if Nat.Coprime z.1.val n ∧
            ∀ p : CRTPrimeRange w V, Nat.Coprime (z.2 p).val p.val
          then 1 / (Nat.totient Q : ℝ) else 0) *
          (if z.2 = r then 1 else 0)) =
        if hR : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val then
          (Nat.totient n : ℝ) / (Nat.totient Q : ℝ) else 0 := by
    rw [Fintype.sum_prod_type]
    by_cases hR : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
    · have hinner (u : Fin n) :
          (∑ b : CRTResidues w V,
            (if Nat.Coprime u.val n ∧
                ∀ p : CRTPrimeRange w V, Nat.Coprime (b p).val p.val
              then 1 / (Nat.totient Q : ℝ) else 0) *
              (if b = r then 1 else 0)) =
            if Nat.Coprime u.val n then 1 / (Nat.totient Q : ℝ) else 0 := by
        let f : CRTResidues w V → ℝ := fun b =>
          if Nat.Coprime u.val n ∧
              ∀ p : CRTPrimeRange w V, Nat.Coprime (b p).val p.val
            then 1 / (Nat.totient Q : ℝ) else 0
        calc
          (∑ b : CRTResidues w V,
              f b * (if b = r then 1 else 0)) =
              ∑ b : CRTResidues w V, if b = r then f r else 0 := by
                apply Finset.sum_congr rfl
                intro b hb
                by_cases hbr : b = r <;> simp [hbr]
          _ = f r := by simp
          _ = if Nat.Coprime u.val n then 1 / (Nat.totient Q : ℝ) else 0 := by
                change (if Nat.Coprime u.val n ∧
                    ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
                  then 1 / (Nat.totient Q : ℝ) else 0) = _
                by_cases hu : Nat.Coprime u.val n
                · rw [if_pos ⟨hu, hR⟩, if_pos hu]
                · rw [if_neg (fun h => hu h.1), if_neg hu]
      simp_rw [hinner]
      have hsumU :
        (∑ u : Fin n, if Nat.Coprime u.val n then
            1 / (Nat.totient Q : ℝ) else 0) =
            ∑ u : Fin n, (1 / (Nat.totient Q : ℝ)) *
              (if Nat.Coprime u.val n then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro u hu
                by_cases hu' : Nat.Coprime u.val n <;> simp [hu']
      have hsumU' :
          (∑ u : Fin n, (1 / (Nat.totient Q : ℝ)) *
              (if Nat.Coprime u.val n then 1 else 0)) =
            (1 / (Nat.totient Q : ℝ)) *
            ∑ u : Fin n, if Nat.Coprime u.val n then 1 else 0 := by
              rw [Finset.mul_sum]
      have hres :
          (∑ u : Fin n, if Nat.Coprime u.val n then
              1 / (Nat.totient Q : ℝ) else 0) =
            (Nat.totient n : ℝ) / (Nat.totient Q : ℝ) := by
        calc
          _ = (1 / (Nat.totient Q : ℝ)) *
              ∑ u : Fin n, if Nat.Coprime u.val n then 1 else 0 := hsumU.trans hsumU'
          _ = (Nat.totient n : ℝ) / (Nat.totient Q : ℝ) := by
                rw [finCoprimeIndicator_sum_eq_totient]
                ring
      rw [dif_pos hR]
      exact hres
    · have hzero (u : Fin n) (b : CRTResidues w V) :
        (if Nat.Coprime u.val n ∧
            ∀ p : CRTPrimeRange w V, Nat.Coprime (b p).val p.val
          then 1 / (Nat.totient Q : ℝ) else 0) *
          (if b = r then 1 else 0) = 0 := by
        by_cases hbr : b = r
        · subst b
          have hnot : ¬ (Nat.Coprime u.val n ∧
              ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val) :=
            fun h => hR h.2
          change (if Nat.Coprime u.val n ∧
              ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
            then 1 / (Nat.totient Q : ℝ) else 0) *
              (if r = r then 1 else 0) = 0
          rw [if_neg hnot]
          simp
        · simp [hbr]
      simp_rw [hzero]
      rw [dif_neg hR]
      simp
  rw [hsum, hpair]
  by_cases hR : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
  · rw [dif_pos hR]
    have hLaw : uniformCRTResidueLaw r =
        ∏ p : CRTPrimeRange w V, 1 / ((p.val - 1 : ℕ) : ℝ) := by
      unfold uniformCRTResidueLaw
      apply Finset.prod_congr rfl
      intro p hp
      have hup := hR p
      simp [hup]
    rw [hLaw]
    have hprodRpos : 0 <
        ∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ) := by
      apply Finset.prod_pos
      intro p hp
      have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
      have hpgt : 1 < p.val := hpPrime.one_lt
      exact_mod_cast Nat.sub_pos_of_lt hpgt
    have hsmallφ : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    have htotR : (Nat.totient Q : ℝ) =
        (Nat.totient n : ℝ) *
          (∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ)) := by
      exact_mod_cast masterCRTModulus_totient w e V
    have hprodR : (∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ)) ≠ 0 :=
      hprodRpos.ne'
    rw [htotR]
    have hprodInv :
        (∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ)⁻¹) =
          (∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ))⁻¹ := by
      simpa using (Finset.prod_inv_distrib
        (s := (Finset.univ : Finset (CRTPrimeRange w V)))
        (f := fun p : CRTPrimeRange w V => ((p.val - 1 : ℕ) : ℝ)))
    simp only [one_div]
    rw [hprodInv]
    field_simp [hprodR, hsmallφ.ne']
  · obtain ⟨p, hp⟩ := not_forall.mp hR
    rw [dif_neg hR]
    have hLaw : uniformCRTResidueLaw r = 0 := by
      unfold uniformCRTResidueLaw
      rw [Finset.prod_eq_zero (Finset.mem_univ p)]
      simp [hp]
    rw [hLaw]

theorem finiteL1_pushforward_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (μ ν : α → ℝ) :
    finiteL1 (finitePushforwardLaw f μ) (finitePushforwardLaw f ν) ≤ finiteL1 μ ν := by
  classical
  have hdiff (y : β) :
      finitePushforwardLaw f μ y - finitePushforwardLaw f ν y =
        ∑ x, (μ x - ν x) * (if f x = y then 1 else 0) := by
    unfold finitePushforwardLaw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxy : f x = y <;> simp [hxy]
  have hsumAbs (y : β) :
      ∑ x, |(μ x - ν x) * (if f x = y then 1 else 0)| =
        ∑ x, |μ x - ν x| * (if f x = y then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxy : f x = y <;> simp [hxy, abs_mul]
  unfold finiteL1
  calc
    (∑ y, |finitePushforwardLaw f μ y - finitePushforwardLaw f ν y|) =
        ∑ y, |∑ x, (μ x - ν x) * (if f x = y then 1 else 0)| := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hdiff]
    _ ≤ ∑ y, ∑ x, |(μ x - ν x) * (if f x = y then 1 else 0)| :=
      Finset.sum_le_sum fun y hy => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, ∑ x, |μ x - ν x| * (if f x = y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hsumAbs y
    _ = ∑ x, ∑ y, |μ x - ν x| * (if f x = y then 1 else 0) := Finset.sum_comm
    _ = ∑ x, |μ x - ν x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum]
      simp

theorem finitePushforwardLaw_sum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (μ : α → ℝ) :
    (∑ y, finitePushforwardLaw f μ y) = ∑ x, μ x := by
  classical
  unfold finitePushforwardLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.mul_sum]
  simp

theorem finModIndicator_sum_eq_one {Q p : ℕ} [NeZero Q] :
    (∑ a : Fin Q, if p % Q = a.val then (1 : ℝ) else 0) = 1 := by
  classical
  let a₀ : Fin Q := ⟨p % Q, Nat.mod_lt _ (NeZero.pos Q)⟩
  have hcond (a : Fin Q) : p % Q = a.val ↔ a = a₀ := by
    constructor
    · intro h
      apply Fin.ext
      exact h.symm
    · intro h
      subst a
      rfl
  calc
    (∑ a : Fin Q, if p % Q = a.val then (1 : ℝ) else 0) =
        ∑ a : Fin Q, if a = a₀ then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [hcond]
    _ = 1 := by simp

theorem primePoolResidueLaw_sum_one {lo hi Q : ℕ} [NeZero Q]
    (hMass : 0 < primePoolMass lo hi) :
    (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) = 1 := by
  classical
  let D := primePoolSupport lo hi
  have hres (p : ℕ) :
      (∑ a : Fin Q, if p % Q = a.val then 1 / (p : ℝ) else 0) =
        1 / (p : ℝ) := by
    calc
      (∑ a : Fin Q, if p % Q = a.val then 1 / (p : ℝ) else 0) =
          ∑ a : Fin Q, (1 / (p : ℝ)) *
            (if p % Q = a.val then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              by_cases h : p % Q = a.val <;> simp [h]
      _ = (1 / (p : ℝ)) *
          ∑ a : Fin Q, if p % Q = a.val then 1 else 0 := by
            rw [Finset.mul_sum]
      _ = 1 / (p : ℝ) := by rw [finModIndicator_sum_eq_one]; ring
  calc
    (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) =
        (∑ p ∈ D, 1 / (p : ℝ)) / primePoolMass lo hi := by
          unfold primePoolResidueLaw
          change (∑ a ∈ (Finset.univ : Finset (Fin Q)),
            (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
              if p % Q = a.val then 1 / (p : ℝ) else 0) /
                primePoolMass lo hi) = _
          rw [← Finset.sum_div]
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro p hp
          exact hres p
    _ = 1 := by
      have hmass : (∑ p ∈ D, 1 / (p : ℝ)) = primePoolMass lo hi := rfl
      rw [hmass]
      exact div_self hMass.ne'

theorem primePoolResidueLaw_abs_sum_le_one {lo hi Q : ℕ} [NeZero Q] :
    (∑ a : Fin Q, |primePoolResidueLaw lo hi Q a|) ≤ 1 := by
  classical
  let M := primePoolMass lo hi
  have hMnonneg : 0 ≤ M := primePoolMass_nonneg lo hi
  have hnonneg (a : Fin Q) : 0 ≤ primePoolResidueLaw lo hi Q a := by
    unfold primePoolResidueLaw
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
    · exact hMnonneg
  have hsum : (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) =
      if M = 0 then 0 else 1 := by
    by_cases hM : M = 0
    · simp [M, hM, primePoolResidueLaw]
    · have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hM)
      simp [M, hM, primePoolResidueLaw_sum_one hMpos]
  calc
    (∑ a : Fin Q, |primePoolResidueLaw lo hi Q a|) =
        ∑ a : Fin Q, primePoolResidueLaw lo hi Q a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact abs_of_nonneg (hnonneg a)
    _ = if M = 0 then 0 else 1 := hsum
    _ ≤ 1 := by split_ifs <;> norm_num

theorem uniformCRTResidueLaw_sum_one {w V : ℕ} :
    (∑ r : CRTResidues w V, uniformCRTResidueLaw r) = 1 := by
  classical
  have hfactor :
      (∑ r : CRTResidues w V, uniformCRTResidueLaw r) =
        ∏ p : CRTPrimeRange w V,
          ∑ a : Fin p.val,
            if Nat.Coprime a.val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0 := by
    unfold uniformCRTResidueLaw
    symm
    exact Finset.prod_univ_sum
      (t := fun p : CRTPrimeRange w V => (Finset.univ : Finset (Fin p.val)))
      (f := fun p a =>
        if Nat.Coprime a.val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0)
  calc
    (∑ r : CRTResidues w V, uniformCRTResidueLaw r) =
        ∏ p : CRTPrimeRange w V,
          ∑ a : Fin p.val,
            if Nat.Coprime a.val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0 := hfactor
    _ = ∏ p : CRTPrimeRange w V, 1 := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
      have hden : ((p.val - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt |>.ne'
      calc
        (∑ a : Fin p.val,
            if Nat.Coprime a.val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0) =
            (1 / ((p.val - 1 : ℕ) : ℝ)) *
              ∑ a : Fin p.val, if Nat.Coprime a.val p.val then 1 else 0 := by
                calc
                  _ = ∑ a : Fin p.val,
                      (1 / ((p.val - 1 : ℕ) : ℝ)) *
                        (if Nat.Coprime a.val p.val then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro a ha
                        by_cases h : Nat.Coprime a.val p.val <;> simp [h]
                  _ = (1 / ((p.val - 1 : ℕ) : ℝ)) *
                      ∑ a : Fin p.val, if Nat.Coprime a.val p.val then 1 else 0 := by
                        rw [Finset.mul_sum]
        _ = 1 := by
          rw [finCoprimeIndicator_sum_eq_totient, Nat.totient_prime hpPrime]
          field_simp [hden]
    _ = 1 := by simp

theorem uniformCRTResidueLaw_abs_sum_eq_one {w V : ℕ} :
    (∑ r : CRTResidues w V, |uniformCRTResidueLaw r|) = 1 := by
  classical
  have hnonneg (r : CRTResidues w V) : 0 ≤ uniformCRTResidueLaw r := by
    unfold uniformCRTResidueLaw
    apply Finset.prod_nonneg
    intro p hp
    split_ifs <;> positivity
  calc
    (∑ r : CRTResidues w V, |uniformCRTResidueLaw r|) =
        ∑ r : CRTResidues w V, uniformCRTResidueLaw r := by
          apply Finset.sum_congr rfl
          intro r hr
          exact abs_of_nonneg (hnonneg r)
    _ = 1 := uniformCRTResidueLaw_sum_one

noncomputable def primePoolCRTResidueLawSingle (lo hi w e V : ℕ)
    (r : CRTResidues w V) : ℝ :=
  ∑' n : ℕ, primePoolLaw lo hi n *
    (if integerCRTResidues w V n = r then 1 else 0)

theorem primeTupleCRTLaw_eq_prod_single {m w e V : ℕ}
    (lo hi : Fin m → ℕ) (r : Fin m → CRTResidues w V) :
    FromArithmetic.primeTupleCRTLaw lo hi w V r =
      ∏ i, primePoolCRTResidueLawSingle (lo i) (hi i) w e V (r i) := by
  classical
  let D := independentPrimePoolSupport lo hi
  let wt (i : Fin m) (x : ℕ) : ℝ :=
    primePoolLaw (lo i) (hi i) x *
      (if integerCRTResidues w V x = r i then 1 else 0)
  have hfactor (p : Fin m → ℕ) :
      (if (fun i => integerCRTResidues w V (p i)) = r then (1 : ℝ) else 0) =
        ∏ i, if integerCRTResidues w V (p i) = r i then 1 else 0 := by
    by_cases h : (fun i => integerCRTResidues w V (p i)) = r
    · have hcoord : ∀ i, integerCRTResidues w V (p i) = r i := fun i => congrFun h i
      simp [h, hcoord]
    · have hcoord : ¬ ∀ i, integerCRTResidues w V (p i) = r i := by
        intro hall
        exact h (funext hall)
      obtain ⟨i, hi⟩ := not_forall.mp hcoord
      rw [if_neg h]
      rw [Finset.prod_eq_zero (s := Finset.univ)
        (f := fun j : Fin m =>
          if integerCRTResidues w V (p j) = r j then (1 : ℝ) else 0)
        (Finset.mem_univ i)]
      simp [hi]
  have hzero (p : Fin m → ℕ) (hp : p ∉ D) :
      independentPrimePoolMass lo hi p *
        (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0) = 0 := by
    simp [independentPrimePoolMass_zero_of_not_mem_support lo hi p
      (by simpa [D] using hp)]
  have hweight (p : Fin m → ℕ) :
      independentPrimePoolMass lo hi p *
        (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0) =
          ∏ i, wt i (p i) := by
    rw [hfactor p]
    unfold independentPrimePoolMass wt
    symm
    exact Finset.prod_mul_distrib
  have hfinite :
      (∑ p ∈ D, independentPrimePoolMass lo hi p *
        (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0)) =
        ∏ i, ∑ x ∈ primePoolSupport (lo i) (hi i), wt i x := by
    calc
      (∑ p ∈ D, independentPrimePoolMass lo hi p *
          (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0)) =
          ∑ p ∈ D, ∏ i, wt i (p i) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hweight p
      _ = ∏ i, ∑ x ∈ primePoolSupport (lo i) (hi i), wt i x := by
            unfold D independentPrimePoolSupport
            symm
            exact Finset.prod_univ_sum
              (t := fun i => primePoolSupport (lo i) (hi i))
              (f := fun i x => wt i x)
  have hcoord (i : Fin m) :
      (∑ x ∈ primePoolSupport (lo i) (hi i), wt i x) =
        primePoolCRTResidueLawSingle (lo i) (hi i) w e V (r i) := by
    unfold primePoolCRTResidueLawSingle
    symm
    apply tsum_eq_sum
    intro x hx
    simp [wt, primePoolLaw_zero_of_not_mem_support (lo i) (hi i) x hx]
  unfold FromArithmetic.primeTupleCRTLaw
  calc
    (∑' p : Fin m → ℕ,
        independentPrimePoolMass lo hi p *
          (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0)) =
        ∑ p ∈ D, independentPrimePoolMass lo hi p *
          (if (fun i => integerCRTResidues w V (p i)) = r then 1 else 0) :=
      tsum_eq_sum (s := D) hzero
    _ = ∏ i, ∑ x ∈ primePoolSupport (lo i) (hi i), wt i x := hfinite
    _ = ∏ i, primePoolCRTResidueLawSingle (lo i) (hi i) w e V (r i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hcoord i

theorem uniformPrimeTupleCRTLaw_eq_prod_single {m w V : ℕ}
    (r : Fin m → CRTResidues w V) :
    FromArithmetic.uniformPrimeTupleCRTLaw w V r =
      ∏ i, uniformCRTResidueLaw (r i) := by
  rfl

theorem primeCRTModulus_dvd_of_range {w e V : ℕ}
    (p : CRTPrimeRange w V) : p.val ∣ masterCRTModulus w e V := by
  have hprod := masterCRTModulus_eq_option_prod w e V
  have hdvd : masterCRTOptionFactor w e V (some p) ∣
      ∏ o : Option (CRTPrimeRange w V), masterCRTOptionFactor w e V o :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ (some p))
  rw [← hprod] at hdvd
  simpa [masterCRTOptionFactor] using hdvd

theorem integerCRTResidues_mod_masterCRTModulus {w e V : ℕ} (n : ℕ) :
    integerCRTResidues w V (n % masterCRTModulus w e V) = integerCRTResidues w V n := by
  funext p
  apply Fin.ext
  simp only [integerCRTResidues]
  rw [Nat.mod_mod_of_dvd _ (primeCRTModulus_dvd_of_range p)]

theorem primePoolCRTResidueLawSingle_eq_pushforward {lo hi w e V : ℕ}
    (hQ : 0 < masterCRTModulus w e V) (r : CRTResidues w V) :
    primePoolCRTResidueLawSingle lo hi w e V r =
      finitePushforwardLaw
        (fun a : Fin (masterCRTModulus w e V) => integerCRTResidues w V a.val)
        (primePoolResidueLaw lo hi (masterCRTModulus w e V)) r := by
  classical
  let Q := masterCRTModulus w e V
  let D := primePoolSupport lo hi
  have hzero (n : ℕ) (hn : n ∉ D) :
      primePoolLaw lo hi n * (if integerCRTResidues w V n = r then 1 else 0) = 0 := by
    simp [primePoolLaw_zero_of_not_mem_support lo hi n (by simpa [D] using hn)]
  have hterm (n : ℕ) (hn : n ∈ D) :
      primePoolLaw lo hi n = (1 / (n : ℝ)) / primePoolMass lo hi := by
    rcases Finset.mem_filter.mp hn with ⟨hI, hp⟩
    rcases Finset.mem_Ico.mp hI with ⟨hlo, hhi⟩
    simp [primePoolLaw, hlo, hhi, hp]
  have hfiber (n : ℕ) (hn : n ∈ D) :
      ∑ a : Fin Q,
        (if n % Q = a.val then (1 / (n : ℝ)) / primePoolMass lo hi else 0) *
          (if integerCRTResidues w V a.val = r then 1 else 0) =
        primePoolLaw lo hi n * (if integerCRTResidues w V n = r then 1 else 0) := by
    let a₀ : Fin Q := ⟨n % Q, Nat.mod_lt _ (by simpa [Q] using hQ)⟩
    have hcond (a : Fin Q) : n % Q = a.val ↔ a = a₀ := by
      constructor
      · intro h
        apply Fin.ext
        exact h.symm
      · intro h
        subst a
        rfl
    have hcrt : integerCRTResidues w V a₀.val = integerCRTResidues w V n := by
      simpa [a₀, Q] using
        integerCRTResidues_mod_masterCRTModulus (w := w) (e := e) (V := V) n
    calc
      (∑ a : Fin Q,
        (if n % Q = a.val then (1 / (n : ℝ)) / primePoolMass lo hi else 0) *
          (if integerCRTResidues w V a.val = r then 1 else 0)) =
        ∑ a : Fin Q, if a = a₀ then (1 / (n : ℝ)) / primePoolMass lo hi *
          (if integerCRTResidues w V a.val = r then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hEq : integerCRTResidues w V a.val = r <;>
            simp [hcond a, hEq]
      _ = (1 / (n : ℝ)) / primePoolMass lo hi *
          (if integerCRTResidues w V n = r then 1 else 0) := by
          simp [a₀, hcrt]
      _ = primePoolLaw lo hi n *
          (if integerCRTResidues w V n = r then 1 else 0) := by
          rw [← hterm n hn]
  have hpush :
      finitePushforwardLaw
        (fun a : Fin Q => integerCRTResidues w V a.val)
        (primePoolResidueLaw lo hi Q) r =
        ∑ n ∈ D, primePoolLaw lo hi n *
          (if integerCRTResidues w V n = r then 1 else 0) := by
    unfold finitePushforwardLaw
    change (∑ a : Fin Q,
        ((∑ n ∈ D, if n % Q = a.val then 1 / (n : ℝ) else 0) /
          primePoolMass lo hi) *
          (if integerCRTResidues w V a.val = r then 1 else 0)) = _
    calc
      (∑ a : Fin Q,
        ((∑ n ∈ D, if n % Q = a.val then 1 / (n : ℝ) else 0) /
          primePoolMass lo hi) *
          (if integerCRTResidues w V a.val = r then 1 else 0)) =
        ∑ a : Fin Q, ∑ n ∈ D,
          ((if n % Q = a.val then 1 / (n : ℝ) else 0) /
            primePoolMass lo hi) *
            (if integerCRTResidues w V a.val = r then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_div, Finset.sum_mul]
      _ = ∑ n ∈ D, ∑ a : Fin Q,
          ((if n % Q = a.val then 1 / (n : ℝ) else 0) /
            primePoolMass lo hi) *
            (if integerCRTResidues w V a.val = r then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ n ∈ D, primePoolLaw lo hi n *
          (if integerCRTResidues w V n = r then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          calc
            (∑ a : Fin Q,
              ((if n % Q = a.val then 1 / (n : ℝ) else 0) /
                primePoolMass lo hi) *
                (if integerCRTResidues w V a.val = r then 1 else 0)) =
              ∑ a : Fin Q,
                (if n % Q = a.val then (1 / (n : ℝ)) / primePoolMass lo hi else 0) *
                  (if integerCRTResidues w V a.val = r then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    by_cases h : n % Q = a.val <;> simp [h]
            _ = primePoolLaw lo hi n *
                (if integerCRTResidues w V n = r then 1 else 0) := hfiber n hn
  unfold primePoolCRTResidueLawSingle
  calc
    (∑' n : ℕ,
      primePoolLaw lo hi n * (if integerCRTResidues w V n = r then 1 else 0)) =
      ∑ n ∈ D,
        primePoolLaw lo hi n * (if integerCRTResidues w V n = r then 1 else 0) :=
          tsum_eq_sum (s := D) hzero
    _ = finitePushforwardLaw
        (fun a : Fin Q => integerCRTResidues w V a.val)
        (primePoolResidueLaw lo hi Q) r := hpush.symm

theorem primePoolCRTResidueLawSingle_abs_sum_le_one {lo hi w e V : ℕ}
    (hQ : 0 < masterCRTModulus w e V) :
    (∑ r : CRTResidues w V,
      |primePoolCRTResidueLawSingle lo hi w e V r|) ≤ 1 := by
  classical
  let Q := masterCRTModulus w e V
  letI : NeZero Q := ⟨hQ.ne'⟩
  let f : Fin Q → CRTResidues w V := fun a => integerCRTResidues w V a.val
  have hsource (a : Fin Q) : 0 ≤ primePoolResidueLaw lo hi Q a := by
    unfold primePoolResidueLaw
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
    · exact primePoolMass_nonneg lo hi
  have hpushNonneg (r : CRTResidues w V) :
      0 ≤ finitePushforwardLaw f (primePoolResidueLaw lo hi Q) r := by
    unfold finitePushforwardLaw
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hsource a) (by split_ifs <;> positivity)
  have hsum :
      (∑ r : CRTResidues w V,
        primePoolCRTResidueLawSingle lo hi w e V r) =
        ∑ a : Fin Q, primePoolResidueLaw lo hi Q a := by
    calc
      (∑ r : CRTResidues w V,
          primePoolCRTResidueLawSingle lo hi w e V r) =
        ∑ r : CRTResidues w V,
          finitePushforwardLaw f (primePoolResidueLaw lo hi Q) r := by
            apply Finset.sum_congr rfl
            intro r hr
            exact primePoolCRTResidueLawSingle_eq_pushforward hQ r
      _ = ∑ a : Fin Q, primePoolResidueLaw lo hi Q a :=
        finitePushforwardLaw_sum f (primePoolResidueLaw lo hi Q)
  calc
    (∑ r : CRTResidues w V,
      |primePoolCRTResidueLawSingle lo hi w e V r|) =
        ∑ r : CRTResidues w V,
          primePoolCRTResidueLawSingle lo hi w e V r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hnonneg : 0 ≤ primePoolCRTResidueLawSingle lo hi w e V r := by
            rw [primePoolCRTResidueLawSingle_eq_pushforward hQ r]
            exact hpushNonneg r
          exact abs_of_nonneg hnonneg
    _ = ∑ a : Fin Q, primePoolResidueLaw lo hi Q a := hsum
    _ ≤ 1 := by
      calc
        (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) =
            ∑ a : Fin Q, |primePoolResidueLaw lo hi Q a| := by
              symm
              apply Finset.sum_congr rfl
              intro a ha
              exact abs_of_nonneg (hsource a)
        _ ≤ 1 := primePoolResidueLaw_abs_sum_le_one
          (lo := lo) (hi := hi) (Q := Q)

theorem maskRowDivisorTemplate_law_eq_tail {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (R : Fin r) (N σ : ℕ) :
    divisorTemplateLaw S.core.parameters N (maskRowDivisorTemplate C Sh R) σ =
      parameterTailProductLaw S.core.parameters N (C.block (Sh.row R).anchor).2.val σ := by
  classical
  let T : Finset (Fin K) := (C.block (Sh.row R).anchor).2.val
  have hT : T.card ≤ K := by
    calc
      T.card ≤ Fintype.card (Fin K) := Finset.card_le_univ T
      _ = K := by simp
  have hX : ∀ j, 0 < S.core.parameters.X N j := S.core.parameters.Xpos N
  have hNorm : ∀ j, 0 < harmonicNormalizer (S.core.parameters.X N j)
      (primorial (N + 1)) := by
    intro j
    exact harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N j)
  have hbridge := parameterTailProductLaw_eq_divisorTemplateLaw_ofFinset
    S.core.parameters N T hT hX hNorm σ
  simpa [maskRowDivisorTemplate, T, divisorTemplateLaw] using hbridge.symm

theorem maskEmptyDivisorTemplate_law {K : ℕ}
    (A : OAI.SourceAdmissible.Parameters K) (N σ : ℕ) :
    divisorTemplateLaw A N (maskEmptyDivisorTemplate (K := K)) σ =
      if σ = 1 then 1 else 0 := by
  classical
  have hformula (X : Fin 0 → ℕ) :
      harmonicProductLaw (primorial (N + 1)) X σ = if σ = 1 then 1 else 0 := by
    unfold harmonicProductLaw
    let t₀ : Fin 0 → ℕ := fun i => Fin.elim0 i
    rw [tsum_eq_single t₀]
    · simp [t₀, eq_comm]
    · intro t ht
      have hEq : t = t₀ := Subsingleton.elim _ _
      exact (ht hEq).elim
  change harmonicProductLaw (primorial (N + 1))
      (fun i : Fin 0 => A.X N ((maskEmptyDivisorTemplate (K := K)).cutoff i)) σ = _
  exact hformula _

theorem nuB_unitLaw_eq_one (y : ℤ) :
    nuB (fun σ : ℕ => if σ = 1 then (1 : ℝ) else 0) y = 1 := by
  unfold nuB
  rw [tsum_eq_single 1]
  · simp
  · intro σ hσ
    simp [hσ]

theorem harmonicResidueError_mono (X W k K : ℕ) (hX : 0 < X)
    (hlog : Real.log (X : ℝ) > (W : ℝ) / X) (hk : k ≤ K) :
    harmonicResidueError X W k ≤ harmonicResidueError X W K := by
  unfold harmonicResidueError
  have hXr : 0 < (X : ℝ) := by exact_mod_cast hX
  have hden : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X) :=
    mul_pos hXr (sub_pos.mpr hlog)
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hk 1

noncomputable def maskWeightedLinearFormsData
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (I : Finset (Fin r)) :
    WeightedLinearFormsData (q := r) (d := m) (b := K) (m := s) S := by
  classical
  let Vseq : ℕ → ℕ := fun N => masterScaleV S.core.parameters N C.gap
  let coeff : ℕ → (Fin s → ℕ) → Fin r → Fin m → ℚ := fun N p R j =>
    rowShapeLinearCoefficients Sh ι
      (chainScale S.core.parameters C a N) N p R j
  let divT : Fin r → DivisorTemplate K K := fun R =>
    if R ∈ I then maskRowDivisorTemplate C Sh R else maskEmptyDivisorTemplate
  let epsBase : ℕ → ℝ := fun N => pivotBaseResidueErrorSum (r := r) S C N
  let epsCRT : ℕ → ℝ := fun N =>
    (s : ℝ) * finiteL1
      (primePoolResidueLaw (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper
        (masterCRTModulus (N + 1) (S.primeStage.e0 N) (Vseq N)))
      (uniformUnitResidueLaw
        (masterCRTModulus (N + 1) (S.primeStage.e0 N) (Vseq N)))
  have hdivSupport (N : ℕ) (R : Fin r) (σ : ℕ)
      (hσ : divisorTemplateLaw S.core.parameters N (divT R) σ ≠ 0) :
      1 ≤ σ ∧ σ ≤ Vseq N := by
    by_cases hR : R ∈ I
    · have htail :
      parameterTailProductLaw S.core.parameters N
            (C.block (Sh.row R).anchor).2.val σ ≠ 0 := by
        have hdivEq : divisorTemplateLaw S.core.parameters N (divT R) σ =
            divisorTemplateLaw S.core.parameters N (maskRowDivisorTemplate C Sh R) σ := by
          simp [divT, hR]
        rw [hdivEq] at hσ
        rw [maskRowDivisorTemplate_law_eq_tail S C Sh R N σ] at hσ
        exact hσ
      exact chainWeight_support S C N (Sh.row R).anchor σ htail
    · have heq : divisorTemplateLaw S.core.parameters N (divT R) σ =
          (if σ = 1 then (1 : ℝ) else 0) := by
        simpa [divT, hR] using
          maskEmptyDivisorTemplate_law S.core.parameters N σ
      have hσone : σ = 1 := by
        by_contra hne
        have hzero : divisorTemplateLaw S.core.parameters N (divT R) σ = 0 := by
          rw [heq]
          simp [hne]
        exact hσ hzero
      constructor
      · simp [hσone]
      · have hV : 2 ≤ Vseq N := by
          dsimp [Vseq]
          unfold masterScaleV
          omega
        rw [hσone]
        omega
  refine {
    gap := fun _ => C.gap
    rowCoeff := coeff
    divisor := divT
    V := Vseq
    epsilonBase := epsBase
    epsilonCRT := epsCRT
    baseMass := fun N _ x => pivotMass S.core.parameters C N x
    goodDomain := fun N p => MaskRowDataGoodDomain S C a Sh ι N p
    V_lower := by
      intro N
      dsimp [Vseq, masterScaleV]
      omega
    V_tendsto := masterScaleV_tendsto_atTop S.core.parameters C.gap
    slot_gap_bound := by
      intro N i
      rfl
    base_nonnegative := by
      intro N p x
      exact pivotMass_nonneg S C N x
    base_normalized := by
      intro N p
      exact pivotMass_tsum_one S C N
    divisor_positive := by
      intro N R σ hσ
      exact (hdivSupport N R σ hσ).1
    divisor_bounded := by
      intro N R σ hσ
      exact (hdivSupport N R σ hσ).2
    base_residue_uniform := by
      intro N p σ hGood hDiv hσ
      have hmodpos : 0 < ∏ u : Fin r, σ u := Finset.prod_pos fun u _ => hσ u
      have hcopEach (u : Fin r) : Nat.Coprime (σ u) (primorial (N + 1)) := by
        apply harmonicProductLaw_coprime_of_ne_zero
          (primorial (N + 1))
          (fun j => S.core.parameters.X N ((divT u).cutoff j)) (σ u)
        simpa [divisorTemplateLaw] using hDiv u
      have hcop : Nat.Coprime (∏ u : Fin r, σ u) (primorial (N + 1)) := by
        rw [Nat.coprime_fintype_prod_left_iff]
        exact hcopEach
      have hmodle : (∏ u : Fin r, σ u) ≤ Vseq N ^ r := by
        calc
          (∏ u : Fin r, σ u) ≤ ∏ u : Fin r, Vseq N := by
            apply Finset.prod_le_prod
            intro u hu
            exact (hdivSupport N u (σ u) (hDiv u)).2
          _ = Vseq N ^ r := by simp
      have hX : ∀ i : Fin m, 2 ≤ S.core.parameters.X N (C.block i).1 := by
        intro i
        have hcut := S.gapStage.valid_raw_cutoffs N (C.block i).1
        have hW : 1 ≤ primorial (N + 1) :=
          Nat.one_le_iff_ne_zero.mpr (primorial_pos (N + 1)).ne'
        omega
      have hlog := hGood.1
      have hbase := pivotBaseResidueLaw_finiteL1_le_sum_sampling_errors
        S C N (∏ u : Fin r, σ u) hmodpos hcop hX hlog
      calc
        finiteL1
            (FromArithmetic.baseResidueLaw (∏ u : Fin r, σ u) hmodpos
              (pivotMass S.core.parameters C N))
            (uniformBaseResidueLaw (∏ u : Fin r, σ u) m) ≤
            ∑ i : Fin m,
              harmonicResidueError (S.core.parameters.X N (C.block i).1)
                (primorial (N + 1)) (∏ u : Fin r, σ u) := hbase
        _ ≤ ∑ i : Fin m,
              harmonicResidueError (S.core.parameters.X N (C.block i).1)
                (primorial (N + 1)) (Vseq N ^ r) := by
              apply Finset.sum_le_sum
              intro i hi
              exact harmonicResidueError_mono
                (S.core.parameters.X N (C.block i).1) (primorial (N + 1))
                (∏ u : Fin r, σ u) (Vseq N ^ r)
                (S.core.parameters.Xpos N (C.block i).1) (hlog i) hmodle
        _ = epsBase N := by
              simp [epsBase, Vseq, pivotBaseResidueErrorSum,
                FromArithmetic.harmonicResidueUniformError]
    row_integer_on_support := by
      intro N p x hGood hx R
      have hrow := hGood.2.1 R p x
      change (FromArithmetic.linearRowValue
        (rowShapeLinearCoefficients Sh ι (chainScale S.core.parameters C a N))
        N p R x).den = 1
      rw [linearRowValue_rowShape]
      exact hrow
    row_denominators_are_units := by
      intro N p hGood v hv hNv hvV R j
      have hden := hGood.2.2.1 R j
      simp [coeff, hden]
    row_primitive := by
      intro N p hGood v hv hNv hvV R
      rcases hGood with ⟨_, _, _, hAnchor, _, hSupport, _⟩
      exact ⟨(Sh.row R).anchor, hAnchor p hSupport v hv hNv hvV R⟩
    pairwise_row_tests := by
      intro N p hGood v hv hNv hvV havoid R J hRJ
      rcases hGood with ⟨_, _, _, _, hPair, hSupport, _⟩
      exact hPair p hSupport v hv hNv hvV havoid R J hRJ
    crt_error_bound := by
      intro N
      let lo := (S.primeStage.pool N C.gap).lower
      let hi := (S.primeStage.pool N C.gap).upper
      let w := N + 1
      let eN := S.primeStage.e0 N
      let Vn := Vseq N
      let Q := masterCRTModulus w eN Vn
      have hQ : 0 < Q := by
        dsimp [Q, w, eN, Vn, Vseq]
        unfold masterCRTModulus
        apply Nat.mul_pos
        · exact pow_pos (primorial_pos (N + 1)) (S.primeStage.e0 N)
        · apply Finset.prod_pos
          intro p hp
          exact (Finset.mem_filter.mp hp).2.pos
      letI : NeZero Q := ⟨hQ.ne'⟩
      let f : Fin Q → CRTResidues w Vn := fun a => integerCRTResidues w Vn a.val
      let μ : Fin s → CRTResidues w Vn → ℝ := fun _ =>
        primePoolCRTResidueLawSingle lo hi w eN Vn
      let ν : Fin s → CRTResidues w Vn → ℝ := fun _ => uniformCRTResidueLaw
      let Err : ℝ := finiteL1 (primePoolResidueLaw lo hi Q)
        (uniformUnitResidueLaw Q)
      have hactual (R : Fin s → CRTResidues w Vn) :
          FromArithmetic.primeTupleCRTLaw
            (fun _ : Fin s => lo) (fun _ : Fin s => hi) w Vn R =
              ∏ i, μ i (R i) := by
        simpa [μ] using
          primeTupleCRTLaw_eq_prod_single
            (fun _ : Fin s => lo) (fun _ : Fin s => hi) R
      have huniform (R : Fin s → CRTResidues w Vn) :
          FromArithmetic.uniformPrimeTupleCRTLaw w Vn R =
            ∏ i, ν i (R i) := by
        simpa [ν] using uniformPrimeTupleCRTLaw_eq_prod_single R
      have hμnorm (i : Fin s) :
          (∑ R : CRTResidues w Vn, |μ i R|) ≤ 1 := by
        simpa [μ] using
          primePoolCRTResidueLawSingle_abs_sum_le_one
            (lo := lo) (hi := hi) (w := w) (e := eN) (V := Vn) hQ
      have hνnorm (i : Fin s) :
          (∑ R : CRTResidues w Vn, |ν i R|) = 1 := by
        simpa [ν] using uniformCRTResidueLaw_abs_sum_eq_one
      have hμeq (i : Fin s) :
          μ i = finitePushforwardLaw f (primePoolResidueLaw lo hi Q) := by
        funext R
        simpa [μ, f] using
          (primePoolCRTResidueLawSingle_eq_pushforward
            (lo := lo) (hi := hi) (w := w) (e := eN) (V := Vn) hQ R)
      have hνeq (i : Fin s) :
          ν i = finitePushforwardLaw f (uniformUnitResidueLaw Q) := by
        funext R
        simpa [ν, f, Q] using
          (uniformUnitResidueLaw_pushforward
            (w := w) (e := eN) (V := Vn) R).symm
      have herr (i : Fin s) : finiteL1 (μ i) (ν i) ≤ Err := by
        calc
          finiteL1 (μ i) (ν i) =
              finiteL1
                (finitePushforwardLaw f (primePoolResidueLaw lo hi Q))
                (finitePushforwardLaw f (uniformUnitResidueLaw Q)) := by
                  rw [hμeq i, hνeq i]
          _ ≤ Err := by
                exact finiteL1_pushforward_le f
                  (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q)
      have htel := FromArithmetic.finite_product_l1_telescoping μ ν
      have hmax (i : Fin s) :
          max (∑ R : CRTResidues w Vn, |μ i R|)
            (∑ R : CRTResidues w Vn, |ν i R|) = 1 := by
        rw [hνnorm i]
        exact max_eq_right (hμnorm i)
      have htuple :
          finiteL1
            (FromArithmetic.primeTupleCRTLaw
              (fun _ : Fin s => lo) (fun _ : Fin s => hi) w Vn)
            (FromArithmetic.uniformPrimeTupleCRTLaw w Vn) ≤
              (s : ℝ) * Err := by
        calc
          finiteL1
              (FromArithmetic.primeTupleCRTLaw
                (fun _ : Fin s => lo) (fun _ : Fin s => hi) w Vn)
              (FromArithmetic.uniformPrimeTupleCRTLaw w Vn) =
            finiteL1 (fun R : Fin s → CRTResidues w Vn => ∏ i, μ i (R i))
              (fun R => ∏ i, ν i (R i)) := by
                rw [show FromArithmetic.primeTupleCRTLaw
                    (fun _ : Fin s => lo) (fun _ : Fin s => hi) w Vn =
                      (fun R : Fin s → CRTResidues w Vn => ∏ i, μ i (R i)) from
                    funext hactual]
                rw [show FromArithmetic.uniformPrimeTupleCRTLaw w Vn =
                    (fun R : Fin s → CRTResidues w Vn => ∏ i, ν i (R i)) from
                    funext huniform]
          _ ≤ ∑ i : Fin s, finiteL1 (μ i) (ν i) := by
                calc
                  finiteL1 (fun R : Fin s → CRTResidues w Vn => ∏ i, μ i (R i))
                      (fun R => ∏ i, ν i (R i)) ≤
                    ∑ i, finiteL1 (μ i) (ν i) *
                      ∏ j ∈ Finset.univ.erase i,
                        max (∑ R, |μ j R|) (∑ R, |ν j R|) := htel
                  _ = ∑ i : Fin s, finiteL1 (μ i) (ν i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [show ∏ j ∈ Finset.univ.erase i,
                        max (∑ R : CRTResidues w Vn, |μ j R|)
                          (∑ R : CRTResidues w Vn, |ν j R|) = 1 by
                      apply Finset.prod_eq_one
                      intro j hj
                      exact hmax j]
                    ring
          _ ≤ ∑ i : Fin s, Err :=
                Finset.sum_le_sum (fun i hi => herr i)
          _ = (s : ℝ) * Err := by simp [Err]
      simpa [epsCRT, Vseq, lo, hi, w, eN, Vn, Q, Err] using htuple
    epsilonBase_superpolynomial := by
      simpa [epsBase] using
        pivotBaseResidueErrorSum_superPolynomialSmall (r := r) S C
    epsilonCRT_superpolynomial := by
      intro A hA
      have herr := S.primeStage.pool_residue_error C.gap A hA
      have hconst : Tendsto (fun N => (s : ℝ) *
          (finiteL1
            (primePoolResidueLaw (S.primeStage.pool N C.gap).lower
              (S.primeStage.pool N C.gap).upper
              (masterCRTModulus (N + 1) (S.primeStage.e0 N)
                (masterScaleV S.core.parameters N C.gap)))
            (uniformUnitResidueLaw
              (masterCRTModulus (N + 1) (S.primeStage.e0 N)
                (masterScaleV S.core.parameters N C.gap))) *
              (masterScaleV S.core.parameters N C.gap : ℝ) ^ A))
          atTop (nhds 0) := by
        have hmul :=
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (s : ℝ)) atTop (nhds (s : ℝ))).mul herr
        simpa [mul_assoc] using hmul
      simpa [epsCRT, Vseq, mul_assoc] using hconst
  }

noncomputable def maskRowSubsetAverage {K s m q r : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s) (I : Finset (Fin r)) : ℝ :=
  gapSlotAverage S C.gap N fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R ∈ I,
        atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i))
            (fun k => (z k : ℚ)))

theorem maskWeightedLinearFormsAverage_eq_subsetAverage_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (I : Finset (Fin r)) :
    ∀ᶠ N in atTop,
      FromArithmetic.weightedLinearFormsAverage
          (maskWeightedLinearFormsData S C a ha Sh ι hlisted I) N
          (fun p => p ∈ independentPrimePoolSupport
            (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
            (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)) =
        maskRowSubsetAverage S C a N Sh ι I := by
  classical
  let D := maskWeightedLinearFormsData S C a ha Sh ι hlisted I
  have hgood := maskRowDataGoodDomain_eventually S C a ha Sh ι hlisted
  have hrowden := rowForm_den_one_eventually (q := q) S C a ha
  have hdivisor (R : Fin r) : D.divisor R =
      if R ∈ I then maskRowDivisorTemplate C Sh R else maskEmptyDivisorTemplate := rfl
  have hcoeff (N : ℕ) (p : Fin s → ℕ) (R : Fin r) (j : Fin m) :
      D.rowCoeff N p R j = rowShapeLinearCoefficients Sh ι
        (chainScale S.core.parameters C a N) N p R j := rfl
  filter_upwards [hgood, hrowden] with N hgood hrowden
  let E : (Fin s → ℕ) → Prop := fun p => p ∈ independentPrimePoolSupport
    (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)
  have hν (p : Fin s → ℕ) (z : Fin m → ℤ) (R : Fin r)
      (hp : E p) :
      nuB (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
          (FromArithmetic.linearRowValue D.rowCoeff N p R z).num =
        if R ∈ I then chainWeight S.core.parameters C N (Sh.row R).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ))).num else 1 := by
    by_cases hR : R ∈ I
    · have hlaw : FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R) =
          parameterTailProductLaw S.core.parameters N (C.block (Sh.row R).anchor).2.val := by
        rw [hdivisor, if_pos hR]
        funext σ
        exact maskRowDivisorTemplate_law_eq_tail S C Sh R N σ
      have hrowval : FromArithmetic.linearRowValue D.rowCoeff N p R z =
          rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ)) := by
        calc
          FromArithmetic.linearRowValue D.rowCoeff N p R z =
              FromArithmetic.linearRowValue
                (rowShapeLinearCoefficients Sh ι
                  (chainScale S.core.parameters C a N)) N p R z := by
                  unfold FromArithmetic.linearRowValue
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hcoeff N p R j]
          _ = rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                (fun i => p (ι i)) (fun k => (z k : ℚ)) :=
                linearRowValue_rowShape Sh ι (chainScale S.core.parameters C a N) N p R z
      rw [hlaw, hrowval]
      simp [chainWeight, hR]
    · have hlaw : FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R) =
          (fun σ => if σ = 1 then 1 else 0) := by
        rw [hdivisor, if_neg hR]
        funext σ
        exact maskEmptyDivisorTemplate_law S.core.parameters N σ
      rw [hlaw]
      simp [hR, nuB_unitLaw_eq_one]
  unfold FromArithmetic.weightedLinearFormsAverage maskRowSubsetAverage gapSlotAverage
  apply tsum_congr
  intro p
  have hmassEq :
      independentPrimePoolMass
        (fun i => (S.primeStage.pool N (D.gap i)).lower)
        (fun i => (S.primeStage.pool N (D.gap i)).upper) p =
      gapSlotMass S C.gap N p := by
    simp [D, maskWeightedLinearFormsData, gapSlotMass]
  rw [hmassEq]
  by_cases hp : E p
  · simp only [E, hp, if_pos, one_mul, mul_one]
    apply congrArg (fun x : ℝ => gapSlotMass S C.gap N p * x)
    apply tsum_congr
    intro z
    have hprod :
        (∏ R : Fin r,
          nuB (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
            (FromArithmetic.linearRowValue D.rowCoeff N p R z).num) =
        ∏ R ∈ I,
          chainWeight S.core.parameters C N (Sh.row R).anchor
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
      calc
        _ = ∏ R : Fin r, if R ∈ I then
              chainWeight S.core.parameters C N (Sh.row R).anchor
                (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                  (fun i => p (ι i)) (fun k => (z k : ℚ))).num else 1 := by
                apply Finset.prod_congr rfl
                intro R hR
                exact hν p z R hp
        _ = ∏ R ∈ I,
              chainWeight S.core.parameters C N (Sh.row R).anchor
                (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                  (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
                simp [Finset.prod_ite_mem]
    have hrow (R : Fin r) :
        atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))) =
          chainWeight S.core.parameters C N (Sh.row R).anchor
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
      have hden := hrowden (Sh.row R) (fun i => p (ι i)) z
      simp [atQ, hden]
    have hprod' :
        (∏ R ∈ I,
          atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ)))) =
        ∏ R ∈ I,
          chainWeight S.core.parameters C N (Sh.row R).anchor
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
      apply Finset.prod_congr rfl
      intro R hR
      exact hrow R
    change pivotMass S.core.parameters C N z *
        (∏ R : Fin r,
          nuB (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
            (FromArithmetic.linearRowValue D.rowCoeff N p R z).num) =
      pivotMass S.core.parameters C N z *
        (∏ R ∈ I,
          atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))))
    rw [hprod, hprod']
  · have hzero := independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper) p hp
    have hgapZero : gapSlotMass S C.gap N p = 0 := by
      simpa [gapSlotMass] using hzero
    simp [E, hp, hzero, hgapZero]

theorem independentPrimePoolProbability_support_eq_one {q : ℕ}
    (lo hi : Fin q → ℕ) (hMass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    independentPrimePoolProbability lo hi
      (fun p => p ∈ independentPrimePoolSupport lo hi) = 1 := by
  classical
  letI : DecidablePred (fun p : Fin q → ℕ => p ∈ independentPrimePoolSupport lo hi) :=
    Classical.decPred _
  unfold independentPrimePoolProbability
  calc
    (∑' p : Fin q → ℕ,
        independentPrimePoolMass lo hi p *
          (if p ∈ independentPrimePoolSupport lo hi then 1 else 0)) =
      ∑' p : Fin q → ℕ, independentPrimePoolMass lo hi p := by
        apply tsum_congr
        intro p
        by_cases hp : p ∈ independentPrimePoolSupport lo hi
        · simp [hp]
        · have hzero := independentPrimePoolMass_zero_of_not_mem_support lo hi p hp
          simp [hp, hzero]
    _ = 1 := independentPrimePoolMass_tsum_one lo hi hMass

theorem maskRowSubsetAverage_le_two_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (I : Finset (Fin r)) :
    ∀ᶠ N in atTop, maskRowSubsetAverage S C a N Sh ι I ≤ 2 := by
  classical
  let D := maskWeightedLinearFormsData S C a ha Sh ι hlisted I
  let E : ℕ → (Fin s → ℕ) → Prop := fun N p => p ∈ independentPrimePoolSupport
    (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)
  obtain ⟨C₀, hC₀, hprop⟩ := FromArithmetic.prop_linear_forms D
  have hgood := maskRowDataGoodDomain_eventually S C a ha Sh ι hlisted
  have hrowEq := maskWeightedLinearFormsAverage_eq_subsetAverage_eventually
    S C a ha Sh ι hlisted I
  have hpoolMass := primePoolMass_pos_eventually S C.gap
  have hlogs : ∀ᶠ N in atTop, ∀ i : Fin m,
      Real.log (S.core.parameters.X N (C.block i).1 : ℝ) >
        (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1 :=
    Filter.eventually_all.2 fun i => pivot_sampling_log_condition_eventually S C i
  have hbaseNonneg : ∀ᶠ N in atTop, 0 ≤ D.epsilonBase N := by
    filter_upwards [hlogs] with N hN
    change 0 ≤ pivotBaseResidueErrorSum (r := r) S C N
    unfold pivotBaseResidueErrorSum
    apply Finset.sum_nonneg
    intro i hi
    have hXpos : (0 : ℝ) < (S.core.parameters.X N (C.block i).1 : ℝ) := by
      exact_mod_cast S.core.parameters.Xpos N (C.block i).1
    have hden : 0 < (S.core.parameters.X N (C.block i).1 : ℝ) *
        (Real.log (S.core.parameters.X N (C.block i).1 : ℝ) -
          (primorial (N + 1) : ℝ) / S.core.parameters.X N (C.block i).1) :=
      mul_pos hXpos (sub_pos.mpr (hN i))
    unfold FromArithmetic.harmonicResidueUniformError
      FromArithmetic.harmonicResidueError
    exact div_nonneg (by positivity) hden.le
  have hcrtNonneg (N : ℕ) : 0 ≤ D.epsilonCRT N := by
    change 0 ≤ (s : ℝ) * finiteL1 _ _
    apply mul_nonneg (by positivity)
    unfold finiteL1
    apply Finset.sum_nonneg
    intro y hy
    exact abs_nonneg _
  have hVone : ∀ᶠ N in atTop, 1 ≤ (D.V N : ℝ) := by
    filter_upwards [D.V_tendsto.eventually_gt_atTop 1] with N hN
    exact_mod_cast hN.le
  have hbasePow : Tendsto
      (fun N => D.epsilonBase N * (D.V N : ℝ) ^ (r : ℝ)) atTop (nhds 0) :=
    D.epsilonBase_superpolynomial.mul_rpow_tendsto hbaseNonneg hVone r
  have hcrtPow : Tendsto
      (fun N => D.epsilonCRT N * (D.V N : ℝ) ^ (r : ℝ)) atTop (nhds 0) :=
    D.epsilonCRT_superpolynomial.mul_rpow_tendsto
      (Filter.Eventually.of_forall hcrtNonneg) hVone r
  have hpow : Tendsto
      (fun N => (D.V N : ℝ) ^ r * (D.epsilonBase N + D.epsilonCRT N))
      atTop (nhds 0) := by
    have hadd := hbasePow.add hcrtPow
    simpa [Real.rpow_natCast, mul_add, mul_comm, mul_left_comm, mul_assoc] using hadd
  have herror : Tendsto
      (fun N : ℕ => C₀ * (1 / ((N + 1 : ℕ) : ℝ) +
        (D.V N : ℝ) ^ r * (D.epsilonBase N + D.epsilonCRT N))) atTop (nhds 0) := by
    have hsum := tendsto_one_div_add_atTop_nhds_zero_nat.add hpow
    simpa using (tendsto_const_nhds.mul hsum)
  have hsmall : ∀ᶠ N in atTop,
      C₀ * (1 / ((N + 1 : ℕ) : ℝ) +
        (D.V N : ℝ) ^ r * (D.epsilonBase N + D.epsilonCRT N)) < 1 :=
    herror.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hprob (N : ℕ)
      (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper) :
      FromArithmetic.weightedLinearFormsEventProbability D N (E N) = 1 := by
    letI : DecidablePred (fun p : Fin s → ℕ => p ∈ independentPrimePoolSupport
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)) := Classical.decPred _
    change independentPrimePoolProbability
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)
      (fun p => p ∈ independentPrimePoolSupport
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)) = 1
    exact independentPrimePoolProbability_support_eq_one
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin s => (S.primeStage.pool N C.gap).upper)
      (fun _ => hMass)
  filter_upwards [hgood, hrowEq, hpoolMass, hsmall]
    with N hgoodN hrowEqN hMassN hsmallN
  have happrox := hprop N (E N) (fun p hp => hgoodN p hp)
  rw [hprob N hMassN] at happrox
  have hsmallN' : C₀ * (1 / ((N : ℝ) + 1) +
      (D.V N : ℝ) ^ r * (D.epsilonBase N + D.epsilonCRT N)) < 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsmallN
  have habs :
      |FromArithmetic.weightedLinearFormsAverage D N (E N) - 1| < 1 :=
    lt_of_le_of_lt happrox hsmallN'
  have hupper : FromArithmetic.weightedLinearFormsAverage D N (E N) ≤ 2 := by
    have h := abs_lt.mp habs
    linarith
  rw [← hrowEqN]
  exact hupper


noncomputable def gapPivotMass {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (p : Fin q → ℕ) (z : Fin m → ℤ) : ℝ :=
  gapSlotMass S C.gap N p * pivotMass S.core.parameters C N z

noncomputable def gapPivotSupport {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) :
    Finset ((Fin q → ℕ) × (Fin m → ℤ)) :=
  independentPrimePoolSupport (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) ×ˢ pivotMassSupport S C N

private theorem gapPivotMass_zero_of_not_mem_support {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (x : (Fin q → ℕ) × (Fin m → ℤ)) (hx : x ∉ gapPivotSupport S C N) :
    gapPivotMass S C N x.1 x.2 = 0 := by
  by_cases hp : x.1 ∈ independentPrimePoolSupport
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  · have hz : x.2 ∉ pivotMassSupport S C N := by
      intro hz
      apply hx
      exact Finset.mem_product.mpr ⟨hp, hz⟩
    simp [gapPivotMass, pivotMass_zero_of_not_mem_support S C N x.2 hz]
  · have hzero := independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) x.1 hp
    simp [gapPivotMass, gapSlotMass, hzero]

theorem gapPivotMass_nonneg {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper) (p : Fin q → ℕ) (z : Fin m → ℤ) :
    0 ≤ gapPivotMass S C N p z := by
  apply mul_nonneg
  · unfold gapSlotMass independentPrimePoolMass
    exact Finset.prod_nonneg fun i _ => primePoolLaw_nonneg _ _ _ hMass
  · exact pivotMass_nonneg S C N z

theorem gapPivotMass_summable {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) :
    Summable (fun x : (Fin q → ℕ) × (Fin m → ℤ) =>
      gapPivotMass S C N x.1 x.2) := by
  classical
  apply summable_of_ne_finset_zero (s := gapPivotSupport S C N)
  intro x hx
  exact gapPivotMass_zero_of_not_mem_support S C N x hx

theorem gapPivotMass_mul_summable {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) :
    Summable (fun x => gapPivotMass S C N x.1 x.2 * F x) := by
  classical
  apply summable_of_ne_finset_zero (s := gapPivotSupport S C N)
  intro x hx
  simp [gapPivotMass_zero_of_not_mem_support S C N x hx]

theorem gapPivotMass_tsum_one {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 = 1 := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let Z := pivotMassSupport S C N
  let D := P ×ˢ Z
  have hPzero (p : Fin q → ℕ) (hp : p ∉ P) : gapSlotMass S C.gap N p = 0 := by
    unfold gapSlotMass
    exact independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  have hZzero (z : Fin m → ℤ) (hz : z ∉ Z) : pivotMass S.core.parameters C N z = 0 :=
    pivotMass_zero_of_not_mem_support S C N z hz
  have hPsum : (∑ p ∈ P, gapSlotMass S C.gap N p) = 1 := by
    calc
      (∑ p ∈ P, gapSlotMass S C.gap N p) = ∑' p : Fin q → ℕ, gapSlotMass S C.gap N p :=
        (tsum_eq_sum (s := P) hPzero).symm
      _ = 1 := gapSlotMass_tsum_one S C.gap N hMass
  have hZsum : (∑ z ∈ Z, pivotMass S.core.parameters C N z) = 1 := by
    calc
      (∑ z ∈ Z, pivotMass S.core.parameters C N z) =
          ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z :=
        (tsum_eq_sum (s := Z) hZzero).symm
      _ = 1 := pivotMass_tsum_one S C N
  have hfinite : (∑ x ∈ D, gapPivotMass S C N x.1 x.2) = 1 := by
    calc
      (∑ x ∈ D, gapPivotMass S C N x.1 x.2) =
          ∑ p ∈ P, ∑ z ∈ Z,
            gapSlotMass S C.gap N p * pivotMass S.core.parameters C N z := by
        dsimp [D, gapPivotMass]
        exact Finset.sum_product' P Z
          (fun p z => gapSlotMass S C.gap N p * pivotMass S.core.parameters C N z)
      _ = ∑ p ∈ P, gapSlotMass S C.gap N p *
          (∑ z ∈ Z, pivotMass S.core.parameters C N z) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
      _ = (∑ p ∈ P, gapSlotMass S C.gap N p) *
          (∑ z ∈ Z, pivotMass S.core.parameters C N z) := by
        rw [Finset.sum_mul]
      _ = 1 := by rw [hPsum, hZsum]; norm_num
  calc
    (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2) =
        ∑ x ∈ D, gapPivotMass S C N x.1 x.2 := by
      apply tsum_eq_sum
      intro x hx
      exact gapPivotMass_zero_of_not_mem_support S C N x hx
    _ = 1 := hfinite

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
    (st : MaskRemovalState m q r) (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ) : Prop :=
  (st.shape.row st.shape.star).support = Jstar ∧
  (∀ U ∈ st.masks, ∀ p y, |st.maskFunction U p y| ≤ 1) ∧
  (∀ R p y, |st.rowFunction R p y| ≤
    1 + chainWeight S.core.parameters C N (st.shape.row R).anchor y) ∧
  ∀ p, st.rowFunction st.shape.star p = gstar

noncomputable def correlation {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) : ℝ :=
  gapSlotAverage S C.gap N fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ((∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)) *
        ∏ R, atQ (st.rowFunction R p)
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
            fun k => (z k : ℚ)))

def pkgMask_stateIntegrand {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (p : Fin q → ℕ) (z : Fin m → ℤ) : ℝ :=
  (∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)) *
    ∏ R, atQ (st.rowFunction R p)
      (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
        fun k => (z k : ℚ))

theorem correlation_empty {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (hmasks : st.masks = ∅) :
    st.correlation S C a N = rowCorrelation S C a N st.shape st.rowFunction := by
  simp [correlation, rowCorrelation, hmasks]

theorem pkgMask_stateCorrelation_joint {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) :
    st.correlation S C a N =
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ),
        gapPivotMass S C N x.1 x.2 *
          ((∏ U ∈ st.masks, st.maskFunction U x.1 (∏ k ∈ U, x.2 k)) *
            ∏ R, atQ (st.rowFunction R x.1)
              (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) x.1
                fun k => (x.2 k : ℚ))) := by
  classical
  let P := independentPrimePoolSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let Z := pivotMassSupport S C N
  let D := P ×ˢ Z
  let F : (Fin q → ℕ) → (Fin m → ℤ) → ℝ := fun p z =>
    (∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)) *
      ∏ R, atQ (st.rowFunction R p)
        (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
          fun k => (z k : ℚ))
  have hPzero (p : Fin q → ℕ) (hp : p ∉ P) : gapSlotMass S C.gap N p = 0 := by
    unfold gapSlotMass
    exact independentPrimePoolMass_zero_of_not_mem_support
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  have hZzero (z : Fin m → ℤ) (hz : z ∉ Z) : pivotMass S.core.parameters C N z = 0 :=
    pivotMass_zero_of_not_mem_support S C N z hz
  have houterZero (p : Fin q → ℕ) (hp : p ∉ P) :
      gapSlotMass S C.gap N p * (∑' z, pivotMass S.core.parameters C N z * F p z) = 0 := by
    rw [hPzero p hp]
    simp
  have hDzero (x : (Fin q → ℕ) × (Fin m → ℤ)) (hx : x ∉ D) :
      gapPivotMass S C N x.1 x.2 * F x.1 x.2 = 0 := by
    rw [gapPivotMass_zero_of_not_mem_support S C N x hx]
    simp
  calc
    st.correlation S C a N =
        ∑ p ∈ P, gapSlotMass S C.gap N p *
          ∑ z ∈ Z, pivotMass S.core.parameters C N z * F p z := by
      unfold MaskRemovalState.correlation gapSlotAverage
      rw [tsum_eq_sum (s := P) houterZero]
      apply Finset.sum_congr rfl
      intro p hp
      rw [tsum_eq_sum (s := Z) (fun z hz => by simp [hZzero z hz])]
    _ = ∑ x ∈ D, gapPivotMass S C N x.1 x.2 * F x.1 x.2 := by
      calc
        (∑ p ∈ P, gapSlotMass S C.gap N p *
            ∑ z ∈ Z, pivotMass S.core.parameters C N z * F p z) =
            ∑ p ∈ P, ∑ z ∈ Z,
              gapSlotMass S C.gap N p * pivotMass S.core.parameters C N z * F p z := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring
        _ = ∑ x ∈ D, gapPivotMass S C N x.1 x.2 * F x.1 x.2 := by
          dsimp [D, gapPivotMass]
          symm
          exact Finset.sum_product' P Z
            (fun p z => gapSlotMass S C.gap N p *
              pivotMass S.core.parameters C N z * F p z)
    _ = ∑' x : (Fin q → ℕ) × (Fin m → ℤ),
          gapPivotMass S C N x.1 x.2 * F x.1 x.2 := by
      symm
      exact tsum_eq_sum (s := D) hDzero
    _ = _ := by rfl

theorem pkgMask_stateCorrelation_coordinate_split {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (u : Fin m) :
    st.correlation S C a N =
      ∑' p : Fin q → ℕ, gapSlotMass S C.gap N p *
        ∑' w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ,
          (∏ i : finsetComplement ({u} : Finset (Fin m)),
            harmonicLaw (S.core.parameters.X N (C.block i.1).1)
              (primorial (N + 1)) (w i)) *
            ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
              (primorial (N + 1)) y *
              ((∏ V ∈ st.masks,
                  st.maskFunction V p
                    (∏ k ∈ V, (pkgMask_coordinateJoin u y w) k)) *
                ∏ R, atQ (st.rowFunction R p)
                  (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
                    fun k => (pkgMask_coordinateJoin u y w k : ℚ))) := by
  classical
  unfold MaskRemovalState.correlation gapSlotAverage
  apply tsum_congr
  intro p
  congr 1
  exact pkgMask_pivotTsum_coordinate_split S C N u (fun z =>
    (∏ V ∈ st.masks, st.maskFunction V p (∏ k ∈ V, z k)) *
      ∏ R, atQ (st.rowFunction R p)
        (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
          fun k => (z k : ℚ)))

noncomputable def pkgMask_stateCoordinatePrimeInsertion {m q r K s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (st : MaskRemovalState m q r) (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ) (u : Fin m) : ℝ :=
  ∑' x : (Fin q → ℕ) ×
      (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
    (gapSlotMass S C.gap N x.1 * pkgMask_pivotRestMass S C N u x.2) *
      poolAverage S C.gap N (fun p =>
        ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
          (primorial (N + 1)) y *
            pkgMask_stateIntegrand st S C a N x.1
              (pkgMask_coordinateJoin u ((p : ℤ) * y) x.2))

theorem pkgMask_stateIntegrand_abs_le {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ)
    (hvalid : st.Valid S C a N Jstar gstar)
    (p : Fin q → ℕ) (z : Fin m → ℤ) :
    |(∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)) *
      ∏ R, atQ (st.rowFunction R p)
        (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
          fun k => (z k : ℚ))| ≤
      (masterScaleV S.core.parameters N C.gap : ℝ) ^ (2 * r) := by
  rcases hvalid with ⟨_, hmask, hrows, _⟩
  have hmaskProd :
      |∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)| ≤ 1 := by
    rw [Finset.abs_prod]
    calc
      (∏ U ∈ st.masks, |st.maskFunction U p (∏ k ∈ U, z k)|) ≤
          ∏ U ∈ st.masks, (1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro U hU
          positivity
        · intro U hU
          exact hmask U hU p _
      _ = 1 := by simp
  have hrowProd := rowProduct_integrand_bound_eventually S C a st.shape N
    st.rowFunction hrows p z
  rw [abs_mul]
  calc
    |∏ U ∈ st.masks, st.maskFunction U p (∏ k ∈ U, z k)| *
        |∏ R, atQ (st.rowFunction R p)
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
            fun k => (z k : ℚ))| ≤
        1 * (masterScaleV S.core.parameters N C.gap : ℝ) ^ (2 * r) := by
          exact mul_le_mul hmaskProd hrowProd (abs_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem pkgMask_stateCoordinateIntegrand_abs_le {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ)
    (hvalid : st.Valid S C a N Jstar gstar) (u : Fin m)
    (p : Fin q → ℕ) (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ)
    (y : ℤ) :
    |(∏ V ∈ st.masks,
          st.maskFunction V p (∏ k ∈ V, (pkgMask_coordinateJoin u y w) k)) *
        ∏ R, atQ (st.rowFunction R p)
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R) p
            fun k => (pkgMask_coordinateJoin u y w k : ℚ))| ≤
      (masterScaleV S.core.parameters N C.gap : ℝ) ^ (2 * r) :=
  pkgMask_stateIntegrand_abs_le st S C a N Jstar gstar hvalid p
    (pkgMask_coordinateJoin u y w)

end MaskRemovalState

noncomputable def outsideBranchMaskRemovalState {K s m q r r' : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u : Fin m)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBranchP u).Parallel ((st.shape.row i).scaleBranchQ u)) ≃ Fin r') :
    MaskRemovalState m (q + 2) r' := by
  let L : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBranchP u
  let R : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBranchQ u
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  have hI : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  refine ⟨Sh', st.masks.erase U,
    (fun V p y => outsideBranchMaskFunction st.maskFunction u V p y), ?_⟩
  intro R' p y
  exact mergedBranchRowFunction
    (fun p => p ∈ independentPrimePoolSupport
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper))
    L R e hI st.rowFunction
    (fun R y => 1 + chainWeight S.core.parameters C N (st.shape.row R).anchor y)
    p R' y

theorem pkgMask_outsideBranchStateIntegrand_identity {K s m q r r' : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u : Fin m)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBranchP u).Parallel
        ((st.shape.row i).scaleBranchQ u)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBranchP u)
      (fun i => (st.shape.row i).scaleBranchQ u) x.val.1 x.val.2)
    (p : Fin (q + 2) → ℕ)
    (hgood : p ∈ independentPrimePoolSupport
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper))
    (z : Fin m → ℤ) (hp : ∀ j, p j ≠ 0)
    (hdenL : ∀ i,
      (rowForm (chainScale S.core.parameters C a N) ((st.shape.row i).scaleBranchP u)
        p fun k => (z k : ℚ)).den = 1)
    (hscaleDen : ∀ i (hi :
        ((st.shape.row i).scaleBranchP u).Parallel ((st.shape.row i).scaleBranchQ u)),
      (RowTemplate.parallelScaleFactor ((st.shape.row i).scaleBranchP u)
        ((st.shape.row i).scaleBranchQ u) hi p *
        ((rowForm (chainScale S.core.parameters C a N)
          ((st.shape.row i).scaleBranchP u) p (fun k => (z k : ℚ))).num : ℚ)).den = 1) :
    (∏ i : Fin r, if hi :
        ((st.shape.row i).scaleBranchP u).Parallel ((st.shape.row i).scaleBranchQ u) then
          1 + chainWeight S.core.parameters C N (st.shape.row i).anchor
            (rowForm (chainScale S.core.parameters C a N)
              ((st.shape.row i).scaleBranchP u) p (fun k => (z k : ℚ))).num
        else 1) *
      MaskRemovalState.pkgMask_stateIntegrand
        (outsideBranchMaskRemovalState S C N st U u Sh' e) S C a N p z =
      ((∏ V ∈ st.masks.erase U,
          st.maskFunction V (dropPrimeTuple2 p)
            (∏ k ∈ V, Function.update z u ((p 1 : ℤ) * z u) k)) *
        ∏ R, atQ (st.rowFunction R (dropPrimeTuple2 p))
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R)
            (dropPrimeTuple2 p)
            (Function.update (fun k => (z k : ℚ)) u ((p 1 : ℚ) * (z u : ℚ))))) *
      ((∏ V ∈ st.masks.erase U,
          st.maskFunction V (dropPrimeTuple2 p)
            (∏ k ∈ V, Function.update z u ((p 0 : ℤ) * z u) k)) *
        ∏ R, atQ (st.rowFunction R (dropPrimeTuple2 p))
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row R)
            (dropPrimeTuple2 p)
            (Function.update (fun k => (z k : ℚ)) u ((p 0 : ℚ) * (z u : ℚ))))) := by
  classical
  let good : (Fin (q + 2) → ℕ) → Prop := fun p => p ∈ independentPrimePoolSupport
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper)
  let L : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBranchP u
  let R : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBranchQ u
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  let hInv : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  let c := chainScale S.core.parameters C a N
  let W : Fin r → ℤ → ℝ := fun i y =>
    1 + chainWeight S.core.parameters C N (st.shape.row i).anchor y
  let Ω : ℝ := ∏ i : Fin r, if hi : I i then
    W i (rowForm c (L i) p (fun k => (z k : ℚ))).num else 1
  let zP : Fin m → ℤ := Function.update z u ((p 1 : ℤ) * z u)
  let zQ : Fin m → ℤ := Function.update z u ((p 0 : ℤ) * z u)
  let maskP : ℝ := ∏ V ∈ st.masks.erase U,
    st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zP k)
  let maskQ : ℝ := ∏ V ∈ st.masks.erase U,
    st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zQ k)
  let rowP : ℝ := ∏ R, atQ (st.rowFunction R (dropPrimeTuple2 p))
    (rowForm c (st.shape.row R) (dropPrimeTuple2 p) (fun k => (zP k : ℚ)))
  let rowQ : ℝ := ∏ R, atQ (st.rowFunction R (dropPrimeTuple2 p))
    (rowForm c (st.shape.row R) (dropPrimeTuple2 p) (fun k => (zQ k : ℚ)))
  have hrow' : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape L R x.val.1 x.val.2 := by
    intro x
    simpa [L, R] using hrow x
  have hWpos : ∀ i y, 0 < W i y := by
    intro i y
    dsimp [W]
    have h := chainWeight_nonneg S C N (st.shape.row i).anchor y
    linarith
  have hWposRow : ∀ i, 0 < W i (rowForm c (L i) p (fun k => (z k : ℚ))).num :=
    fun i => hWpos i _
  have hRows := pkgMask_branchRowProductIdentity st.shape Sh' L R e hInv hrow'
    good st.rowFunction W c p hgood (fun k => (z k : ℚ)) hp
    (by simpa [L, c] using hdenL)
    (by simpa [L, R, c] using hscaleDen) hWposRow
  have hupdate (t : ℕ) :
      (fun k => (Function.update z u ((t : ℤ) * z u) k : ℚ)) =
        Function.update (fun k => (z k : ℚ)) u ((t : ℚ) * (z u : ℚ)) := by
    funext k
    by_cases hk : k = u
    · subst k
      simp [Function.update_self, Int.cast_mul]
    · simp [Function.update_of_ne hk]
  have hformP (j : Fin r) :
      rowForm c (L j) p (fun k => (z k : ℚ)) =
        rowForm c (st.shape.row j) (dropPrimeTuple2 p)
          (fun k => (zP k : ℚ)) := by
    calc
      rowForm c (L j) p (fun k => (z k : ℚ)) =
          rowForm c (st.shape.row j) (dropPrimeTuple2 p)
            (Function.update (fun k => (z k : ℚ)) u ((p 1 : ℚ) * (z u : ℚ))) := by
        simpa [L] using rowForm_scaleBranchP_tuple2 c (st.shape.row j) u p z
      _ = rowForm c (st.shape.row j) (dropPrimeTuple2 p)
          (fun k => (zP k : ℚ)) := by
        congr 1
        exact (hupdate (p 1)).symm
  have hformQ (j : Fin r) :
      rowForm c (R j) p (fun k => (z k : ℚ)) =
        rowForm c (st.shape.row j) (dropPrimeTuple2 p)
          (fun k => (zQ k : ℚ)) := by
    calc
      rowForm c (R j) p (fun k => (z k : ℚ)) =
          rowForm c (st.shape.row j) (dropPrimeTuple2 p)
            (Function.update (fun k => (z k : ℚ)) u ((p 0 : ℚ) * (z u : ℚ))) := by
        simpa [R] using rowForm_scaleBranchQ_tuple2 c (st.shape.row j) u p z
      _ = rowForm c (st.shape.row j) (dropPrimeTuple2 p)
          (fun k => (zQ k : ℚ)) := by
        congr 1
        exact (hupdate (p 0)).symm
  have hRows' : Ω *
      (∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
        st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) =
        rowP * rowQ := by
    calc
      Ω * (∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) =
          (∏ i : Fin r, atQ (st.rowFunction i (dropPrimeTuple2 p))
            (rowForm c (L i) p (fun k => (z k : ℚ)))) *
          ∏ i : Fin r, atQ (st.rowFunction i (dropPrimeTuple2 p))
            (rowForm c (R i) p (fun k => (z k : ℚ))) := hRows
      _ = rowP * rowQ := by
        simp_rw [hformP, hformQ]
        rfl
  have hMasks :
      (∏ V ∈ st.masks.erase U,
        outsideBranchMaskFunction st.maskFunction u V p (∏ k ∈ V, z k)) =
          maskP * maskQ := by
    calc
      _ = ∏ V ∈ st.masks.erase U,
          st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zP k) *
            st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zQ k) := by
        apply Finset.prod_congr rfl
        intro V hV
        simpa [zP, zQ] using
          pkgMask_outsideBranchMask_substitution st.maskFunction u V p z
      _ = maskP * maskQ := by
        simp [maskP, maskQ, Finset.prod_mul_distrib]
  change Ω *
      ((∏ V ∈ st.masks.erase U,
          outsideBranchMaskFunction st.maskFunction u V p (∏ k ∈ V, z k)) *
        ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) = _
  calc
    Ω *
        ((∏ V ∈ st.masks.erase U,
            outsideBranchMaskFunction st.maskFunction u V p (∏ k ∈ V, z k)) *
          ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
            st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) =
        (Ω * ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) *
          (∏ V ∈ st.masks.erase U,
            outsideBranchMaskFunction st.maskFunction u V p (∏ k ∈ V, z k)) := by ring
    _ = (rowP * rowQ) * (maskP * maskQ) := by rw [hRows', hMasks]
    _ = _ := by
      simp only [maskP, maskQ, rowP, rowQ, zP, zQ]
      rw [hupdate (p 1), hupdate (p 0)]
      ring

theorem outsideBranchMaskRemovalState_valid {K s m q r r' : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u : Fin m)
    (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ)
    (hvalid : st.Valid S C a N Jstar gstar)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBranchP u).Parallel
        ((st.shape.row i).scaleBranchQ u)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBranchP u)
      (fun i => (st.shape.row i).scaleBranchQ u) x.val.1 x.val.2)
    (hstarIndex : Sh'.star = e ⟨(st.shape.star, 0), Or.inl rfl⟩)
    (hstarNot : ¬ ((st.shape.row st.shape.star).scaleBranchP u).Parallel
      ((st.shape.row st.shape.star).scaleBranchQ u))
    (hpoolLower : masterScaleV S.core.parameters N C.gap <
      (S.primeStage.pool N C.gap).lower) :
    (outsideBranchMaskRemovalState S C N st U u Sh' e).Valid
      S C a N Jstar gstar := by
  classical
  rcases hvalid with ⟨hstarSupport, hmask, hrowBound, hstarFunction⟩
  let L : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBranchP u
  let R : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBranchQ u
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  let hInv : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  let good : (Fin (q + 2) → ℕ) → Prop := fun p => p ∈ independentPrimePoolSupport
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper)
  let W : Fin r → ℤ → ℝ := fun i y =>
    1 + chainWeight S.core.parameters C N (st.shape.row i).anchor y
  let xstar : RowBranchIndex I := ⟨(st.shape.star, 0), Or.inl rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (Sh'.row Sh'.star).support =
          (Sh'.row (e xstar)).support := by rw [hstarIndex]
      _ = (RowBranchTemplate st.shape L R st.shape.star 0).support :=
        congrArg (fun T : RowTemplate m (q + 2) => T.support)
          (by simpa [L, R] using hrow xstar)
      _ = (L st.shape.star).support := by simp [RowBranchTemplate]
      _ = (st.shape.row st.shape.star).support :=
        (st.shape.row st.shape.star).scaleBranchP_support u
      _ = Jstar := hstarSupport
  · intro V hV p y
    rcases Finset.mem_erase.mp hV with ⟨_, hVold⟩
    change |outsideBranchMaskFunction st.maskFunction u V p y| ≤ 1
    unfold outsideBranchMaskFunction
    rw [abs_mul]
    calc
      |st.maskFunction V (dropPrimeTuple2 p)
          ((if u ∈ V then (p 1 : ℤ) else 1) * y)| *
        |st.maskFunction V (dropPrimeTuple2 p)
          ((if u ∈ V then (p 0 : ℤ) else 1) * y)| ≤ 1 * 1 := by
            exact mul_le_mul
              (hmask V hVold (dropPrimeTuple2 p) _)
              (hmask V hVold (dropPrimeTuple2 p) _)
              (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro R' p y
    let x := e.symm R'
    have hRbranch : (Sh'.row R').support = (st.shape.row x.val.1).support := by
      rw [show R' = e x from by simp [x]]
      rw [show Sh'.row (e x) =
        RowBranchTemplate st.shape L R x.val.1 x.val.2 by simpa [L, R] using hrow x]
      by_cases hzero : x.val.2.val = 0
      · have hb : x.val.2 = 0 := Fin.ext hzero
        simpa [RowBranchTemplate, hb] using
          (st.shape.row x.val.1).scaleBranchP_support u
      · have hone : x.val.2.val = 1 := by omega
        have hb : x.val.2 = 1 := Fin.ext hone
        simpa [RowBranchTemplate, hb] using
          (st.shape.row x.val.1).scaleBranchQ_support u
    have hanchor : (Sh'.row R').anchor = (st.shape.row x.val.1).anchor :=
      RowTemplate.anchor_eq_of_support_eq (Sh'.row R') (st.shape.row x.val.1) hRbranch
    have hWnonneg : ∀ i y, 0 ≤ W i y := by
      intro i y
      dsimp [W]
      have h := chainWeight_nonneg S C N (st.shape.row i).anchor y
      linarith
    have hWpos : ∀ i y, 0 < W i y := by
      intro i y
      dsimp [W]
      have h := chainWeight_nonneg S C N (st.shape.row i).anchor y
      linarith
    have hInvWeight : ∀ i (hi : I i) p' (y : ℤ),
        good p' →
        (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' *
          (y : ℚ)).den = 1 →
        W i (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' *
          (y : ℚ)).num = W i y := by
      intro i hi p' y hgood hden
      have hslots := (independentPrimePoolSupport_mem_iff
        (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper) p').mp hgood
      have hslot (j : Fin (q + 2)) :
          (S.primeStage.pool N C.gap).lower ≤ p' j ∧
            p' j < (S.primeStage.pool N C.gap).upper ∧ (p' j).Prime := by
        rcases Finset.mem_filter.mp (hslots j) with ⟨hIco, hpj⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
        exact ⟨hlo, hhi, hpj⟩
      have hp0 : (p' 0).Prime := (hslot 0).2.2
      have hp1 : (p' 1).Prime := (hslot 1).2.2
      have hV0 : masterScaleV S.core.parameters N C.gap < p' 0 :=
        lt_of_lt_of_le hpoolLower (hslot 0).1
      have hV1 : masterScaleV S.core.parameters N C.gap < p' 1 :=
        lt_of_lt_of_le hpoolLower (hslot 1).1
      have hpall : ∀ j, p' j ≠ 0 := fun j =>
        Nat.ne_of_gt (Nat.Prime.pos (hslot j).2.2)
      have hp1q : (p' 1 : ℚ) ≠ 0 := by exact_mod_cast hpall 1
      by_cases heq : p' 0 = p' 1
      · have hfac : RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' = 1 := by
          change (∏ j, (p' j : ℚ) ^ (Classical.choose (hInv i |>.mp hi).2 j)) = 1
          rw [RowTemplate.scaleBranch_parallel_factor_eq (st.shape.row i) u p' hpall
            (hInv i |>.mp hi)]
          by_cases hsingle : (st.shape.row i).support = {u}
          · simp [hsingle, heq, hp1q]
          · simp [hsingle]
        rw [hfac] at hden ⊢
        simpa [W]
      · have hwt := chainWeight_scaleBranch_invariant S C N
          (st.shape.row i).anchor (st.shape.row i) u p' hpall hp0 hp1 hV0 hV1 heq
          (hInv i |>.mp hi) y hden
        simpa [W, RowTemplate.parallelScaleFactor] using
          congrArg (fun t : ℝ => 1 + t) hwt
    have hbound := mergedBranchRowFunction_abs_le good L R e hInv st.rowFunction W p
      hrowBound hWnonneg hWpos hInvWeight R' y
    simpa [outsideBranchMaskRemovalState, W, hanchor] using hbound
  · intro p
    change mergedBranchRowFunction good L R e hInv st.rowFunction W p Sh'.star = gstar
    rw [hstarIndex]
    have hx : ¬ I st.shape.star := by simpa [I, L, R] using hstarNot
    have hmerged :
        mergedBranchRowFunction good L R e hInv st.rowFunction W p (e xstar) =
          st.rowFunction st.shape.star (dropPrimeTuple2 p) := by
      unfold mergedBranchRowFunction
      simp only [Equiv.symm_apply_apply]
      simp [xstar, I, L, R, hstarNot]
    rw [hmerged]
    exact hstarFunction (dropPrimeTuple2 p)

noncomputable def pkgMask_balancedBranchMaskRemovalState {K s m q r r' : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u v : Fin m)
    (huv : u ≠ v) (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)) ≃ Fin r') :
    MaskRemovalState m (q + 2) r' := by
  let L : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBalancedP u v
  let R : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBalancedQ u v
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  have hI : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  refine ⟨Sh', st.masks.erase U,
    (fun V p y => balancedBranchMaskFunction st.maskFunction u v V p y), ?_⟩
  intro R' p y
  exact mergedBranchRowFunction
    (fun p => p ∈ independentPrimePoolSupport
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper))
    L R e hI st.rowFunction
    (fun R y => 1 + chainWeight S.core.parameters C N (st.shape.row R).anchor y)
    p R' y

theorem pkgMask_balancedBranchMaskRemovalState_valid {K s m q r r' : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u v : Fin m)
    (huv : u ≠ v) (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ)
    (hvalid : st.Valid S C a N Jstar gstar)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBalancedP u v)
      (fun i => (st.shape.row i).scaleBalancedQ u v) x.val.1 x.val.2)
    (hstarIndex : Sh'.star = e ⟨(st.shape.star, 0), Or.inl rfl⟩)
    (hstarNot : ¬ ((st.shape.row st.shape.star).scaleBalancedP u v).Parallel
      ((st.shape.row st.shape.star).scaleBalancedQ u v))
    (hpoolLower : masterScaleV S.core.parameters N C.gap <
      (S.primeStage.pool N C.gap).lower) :
    (pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).Valid
      S C a N Jstar gstar := by
  classical
  rcases hvalid with ⟨hstarSupport, hmask, hrowBound, hstarFunction⟩
  let L : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBalancedP u v
  let R : Fin r → RowTemplate m (q + 2) :=
    fun i => (st.shape.row i).scaleBalancedQ u v
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  let hInv : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  let good : (Fin (q + 2) → ℕ) → Prop := fun p => p ∈ independentPrimePoolSupport
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper)
  let W : Fin r → ℤ → ℝ := fun i y =>
    1 + chainWeight S.core.parameters C N (st.shape.row i).anchor y
  let xstar : RowBranchIndex I := ⟨(st.shape.star, 0), Or.inl rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (Sh'.row Sh'.star).support =
          (Sh'.row (e xstar)).support := by rw [hstarIndex]
      _ = (RowBranchTemplate st.shape L R st.shape.star 0).support :=
        congrArg (fun T : RowTemplate m (q + 2) => T.support)
          (by simpa [L, R] using hrow xstar)
      _ = (L st.shape.star).support := by simp [RowBranchTemplate]
      _ = (st.shape.row st.shape.star).support :=
        (st.shape.row st.shape.star).scaleBalancedP_support u v
      _ = Jstar := hstarSupport
  · intro V hV p y
    rcases Finset.mem_erase.mp hV with ⟨_, hVold⟩
    change |balancedBranchMaskFunction st.maskFunction u v V p y| ≤ 1
    unfold balancedBranchMaskFunction
    rw [abs_mul]
    calc
      |st.maskFunction V (dropPrimeTuple2 p)
          ((if u ∈ V then (p 0 : ℤ) else 1) *
            (if v ∈ V then (p 1 : ℤ) else 1) * y)| *
        |st.maskFunction V (dropPrimeTuple2 p)
          ((if v ∈ V then (p 0 : ℤ) else 1) *
            (if u ∈ V then (p 1 : ℤ) else 1) * y)| ≤ 1 * 1 := by
            exact mul_le_mul
              (hmask V hVold (dropPrimeTuple2 p) _)
              (hmask V hVold (dropPrimeTuple2 p) _)
              (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro R' p y
    let x := e.symm R'
    have hRbranch : (Sh'.row R').support = (st.shape.row x.val.1).support := by
      rw [show R' = e x from by simp [x]]
      rw [show Sh'.row (e x) =
        RowBranchTemplate st.shape L R x.val.1 x.val.2 by simpa [L, R] using hrow x]
      by_cases hzero : x.val.2.val = 0
      · have hb : x.val.2 = 0 := Fin.ext hzero
        simpa [RowBranchTemplate, hb] using
          (st.shape.row x.val.1).scaleBalancedP_support u v
      · have hone : x.val.2.val = 1 := by omega
        have hb : x.val.2 = 1 := Fin.ext hone
        simpa [RowBranchTemplate, hb] using
          (st.shape.row x.val.1).scaleBalancedQ_support u v
    have hanchor : (Sh'.row R').anchor = (st.shape.row x.val.1).anchor :=
      RowTemplate.anchor_eq_of_support_eq (Sh'.row R') (st.shape.row x.val.1) hRbranch
    have hWnonneg : ∀ i y, 0 ≤ W i y := by
      intro i y
      dsimp [W]
      have h := chainWeight_nonneg S C N (st.shape.row i).anchor y
      linarith
    have hWpos : ∀ i y, 0 < W i y := by
      intro i y
      dsimp [W]
      have h := chainWeight_nonneg S C N (st.shape.row i).anchor y
      linarith
    have hInvWeight : ∀ i (hi : I i) p' (y : ℤ),
        good p' →
        (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' *
          (y : ℚ)).den = 1 →
        W i (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' *
          (y : ℚ)).num = W i y := by
      intro i hi p' y hgood hden
      have hslots := (independentPrimePoolSupport_mem_iff
        (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper) p').mp hgood
      have hslot (j : Fin (q + 2)) :
          (S.primeStage.pool N C.gap).lower ≤ p' j ∧
            p' j < (S.primeStage.pool N C.gap).upper ∧ (p' j).Prime := by
        rcases Finset.mem_filter.mp (hslots j) with ⟨hIco, hpj⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
        exact ⟨hlo, hhi, hpj⟩
      have hp0 : (p' 0).Prime := (hslot 0).2.2
      have hp1 : (p' 1).Prime := (hslot 1).2.2
      have hV0 : masterScaleV S.core.parameters N C.gap < p' 0 :=
        lt_of_lt_of_le hpoolLower (hslot 0).1
      have hV1 : masterScaleV S.core.parameters N C.gap < p' 1 :=
        lt_of_lt_of_le hpoolLower (hslot 1).1
      have hpall : ∀ j, p' j ≠ 0 := fun j =>
        Nat.ne_of_gt (Nat.Prime.pos (hslot j).2.2)
      have hp0q : (p' 0 : ℚ) ≠ 0 := by exact_mod_cast hpall 0
      have hp1q : (p' 1 : ℚ) ≠ 0 := by exact_mod_cast hpall 1
      by_cases heq : p' 0 = p' 1
      · have hfac : RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p' = 1 := by
          change (∏ j, (p' j : ℚ) ^ (Classical.choose (hInv i |>.mp hi).2 j)) = 1
          rw [RowTemplate.scaleBalanced_parallel_factor_eq
            (st.shape.row i) u v huv p' hpall (hInv i |>.mp hi)]
          by_cases hsingleU : (st.shape.row i).support = {u}
          · simp [hsingleU, heq, hp0q, hp1q]
          · by_cases hsingleV : (st.shape.row i).support = {v}
            · simp [hsingleU, hsingleV, heq, hp0q, hp1q]
            · simp [hsingleU, hsingleV]
        rw [hfac] at hden ⊢
        simpa [W]
      · have hwt := chainWeight_scaleBalanced_invariant S C N
          (st.shape.row i).anchor (st.shape.row i) u v huv p' hpall hp0 hp1
          hV0 hV1 heq (hInv i |>.mp hi) y hden
        simpa [W, RowTemplate.parallelScaleFactor] using
          congrArg (fun t : ℝ => 1 + t) hwt
    have hbound := mergedBranchRowFunction_abs_le good L R e hInv st.rowFunction W p
      hrowBound hWnonneg hWpos hInvWeight R' y
    simpa [pkgMask_balancedBranchMaskRemovalState, W, hanchor] using hbound
  · intro p
    change mergedBranchRowFunction good L R e hInv st.rowFunction W p Sh'.star = gstar
    rw [hstarIndex]
    have hmerged :
        mergedBranchRowFunction good L R e hInv st.rowFunction W p (e xstar) =
          st.rowFunction st.shape.star (dropPrimeTuple2 p) := by
      unfold mergedBranchRowFunction
      simp only [Equiv.symm_apply_apply]
      simp [xstar, I, L, R, hstarNot]
    rw [hmerged]
    exact hstarFunction (dropPrimeTuple2 p)

theorem exists_maskShape_step {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar U : Finset (Fin m)) (hJ : 2 ≤ Jstar.card)
    (hStar : (Sh.row Sh.star).support = Jstar) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r'),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar := by
  rcases exists_mask_substitution_coordinates Jstar U hJ with
    ⟨u, huJ, huU⟩ | ⟨u, v, huJ, hvJ, huv⟩
  · have hErasePos : 0 < (Jstar.erase u).card := by
      rw [Finset.card_erase_of_mem huJ]
      omega
    obtain ⟨v, hvErase⟩ := Finset.card_pos.mp hErasePos
    rcases Finset.mem_erase.mp hvErase with ⟨hvu, hvJ⟩
    have huSupp : u ∈ (Sh.row Sh.star).support := by rw [hStar]; exact huJ
    have hvSupp : v ∈ (Sh.row Sh.star).support := by rw [hStar]; exact hvJ
    obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
      exists_scaleBranch_row_shape Sh Jstar hStar u v huSupp hvSupp hvu
    exact ⟨r', Sh', hr', hstar'⟩
  · have huSupp : u ∈ (Sh.row Sh.star).support := by rw [hStar]; exact huJ
    have hvSupp : v ∈ (Sh.row Sh.star).support := by rw [hStar]; exact hvJ
    obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
      exists_scaleBalanced_row_shape Sh Jstar hStar u v huSupp hvSupp huv
    exact ⟨r', Sh', hr', hstar'⟩

theorem exists_maskShape_after_list {m : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (masks : List (Finset (Fin m)))
    (hMasks : ∀ U ∈ masks, U.Nonempty) :
    ∃ (q r : ℕ) (Sh : RowShape m q r), q = 2 * masks.length ∧
      r ≤ maskCount m * 2 ^ masks.length ∧ (Sh.row Sh.star).support = Jstar := by
  induction masks with
  | nil =>
    have hStar := initialMaskShape_star_support Jstar hJ
    refine ⟨0, maskCount m, initialMaskShape Jstar hJ, ?_, ?_, hStar⟩
    · simp
    · simp
  | cons U rest ih =>
    have hRest : ∀ V ∈ rest, V.Nonempty := by
      intro V hV
      exact hMasks V (List.mem_cons_of_mem U hV)
    obtain ⟨q, r, Sh, hq, hr, hStar⟩ := ih hRest
    obtain ⟨r', Sh', hr', hStar'⟩ := exists_maskShape_step Sh Jstar U hJ hStar
    refine ⟨q + 2, r', Sh', ?_, ?_, hStar'⟩
    · simp only [List.length_cons]
      omega
    · calc
        r' ≤ 2 * r := hr'
        _ ≤ 2 * (maskCount m * 2 ^ rest.length) := Nat.mul_le_mul_left 2 hr
        _ = maskCount m * 2 ^ (rest.length + 1) := by rw [pow_succ]; ring

def nonemptyMaskFinset (m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter Finset.Nonempty

theorem nonemptyMaskFinset_card (m : ℕ) :
    (nonemptyMaskFinset m).card = maskCount m := by
  classical
  have hcard : Fintype.card {U : Finset (Fin m) // U.Nonempty} =
      (nonemptyMaskFinset m).card := by
    apply Fintype.card_of_subtype (nonemptyMaskFinset m)
    intro U
    simp [nonemptyMaskFinset]
  calc
    (nonemptyMaskFinset m).card = Fintype.card {U : Finset (Fin m) // U.Nonempty} := hcard.symm
    _ = maskCount m := card_nonempty_mask_subsets m

theorem exists_maskRowShape (m : ℕ) (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card) :
    ∃ (q r : ℕ) (Sh : RowShape m q r), q ≤ 2 * maskCount m ∧
      r ≤ maskRowBound m ∧ (Sh.row Sh.star).support = Jstar := by
  classical
  let Ulist := (nonemptyMaskFinset m).toList
  have hMasks : ∀ U ∈ Ulist, U.Nonempty := by
    intro U hU
    have hU' : U ∈ nonemptyMaskFinset m := by simpa [Ulist] using hU
    exact (Finset.mem_filter.mp hU').2
  obtain ⟨q, r, Sh, hq, hr, hstar⟩ :=
    exists_maskShape_after_list Jstar hJ Ulist hMasks
  have hlen : Ulist.length = maskCount m := by
    dsimp [Ulist]
    simp [nonemptyMaskFinset_card]
  refine ⟨q, r, Sh, ?_, ?_, hstar⟩
  · rw [hq, hlen]
  · unfold maskRowBound
    rw [hlen] at hr
    exact hr

theorem exists_maskRowShape_tests (m : ℕ) (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) :
    ∃ (q r : ℕ) (Sh : RowShape m q r)
      (tests : Finset (IntegerPolynomial q)),
      r ≤ maskRowBound m ∧ q ≤ 2 * maskCount m ∧
        (Sh.row Sh.star).support = Jstar ∧ ∀ P ∈ tests, P ≠ 0 := by
  obtain ⟨q, r, Sh, hq, hr, hstar⟩ := exists_maskRowShape m Jstar hJ
  refine ⟨q, r, Sh, templateMinors Sh, hr, hq, hstar, ?_⟩
  intro P hP
  exact (Finset.mem_filter.mp hP).2

theorem initialMaskRemovalState_valid {m K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
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
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
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

theorem abs_mul_div_le_of_abs_le {W f g : ℝ} (hW : 1 ≤ W)
    (hf : |f| ≤ W) (hg : |g| ≤ W) : |f * g / W| ≤ W := by
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hprod : |f| * |g| ≤ W * W :=
    mul_le_mul hf hg (abs_nonneg _) (by positivity)
  rw [abs_div, abs_mul, abs_of_pos hWpos]
  exact (div_le_iff₀ hWpos).2 hprod

theorem gapPivot_weighted_cauchy_schwarz {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    (Ω H₀ H₁ : (Fin q → ℕ) × (Fin m → ℤ) → ℝ)
    (hΩ : ∀ x, 0 ≤ Ω x) (h0 : ∀ x, |H₀ x| ≤ Ω x) :
    |∑' x, gapPivotMass S C N x.1 x.2 * (H₀ x * H₁ x)| ^ 2 ≤
      (∑' x, gapPivotMass S C N x.1 x.2 * Ω x) *
        ∑' x, gapPivotMass S C N x.1 x.2 * (Ω x * H₁ x ^ 2) := by
  apply weighted_cauchy_schwarz_aux
    (μ := fun x => gapPivotMass S C N x.1 x.2) Ω H₀ H₁
  · intro x
    exact gapPivotMass_nonneg S C N hMass x.1 x.2
  · exact hΩ
  · exact h0
  · exact gapPivotMass_mul_summable S C N Ω
  · exact gapPivotMass_mul_summable S C N (fun x => Ω x * H₁ x ^ 2)

end HindmanSumsProducts
