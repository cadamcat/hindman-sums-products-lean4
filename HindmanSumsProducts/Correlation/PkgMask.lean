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
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r'),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar := by
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
  exact ⟨Fintype.card β, Sh', hcard, hstar⟩

theorem exists_scaleBranch_row_shape {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hStarSupport : (Sh.row Sh.star).support = Jstar)
    (u v : Fin m) (hu : u ∈ (Sh.row Sh.star).support)
    (hv : v ∈ (Sh.row Sh.star).support) (hvu : v ≠ u) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r'),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar := by
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
  exact exists_branch_row_shape Sh L R I hI hAcross hStar Jstar hTarget

theorem exists_scaleBalanced_row_shape {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hStarSupport : (Sh.row Sh.star).support = Jstar)
    (u v : Fin m) (hu : u ∈ (Sh.row Sh.star).support)
    (hv : v ∈ (Sh.row Sh.star).support) (huv : u ≠ v) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r'),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar := by
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
  exact exists_branch_row_shape Sh L R I hI hAcross hStar Jstar hTarget

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

theorem correlation_empty {m q r K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (st : MaskRemovalState m q r)
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ) (N : ℕ)
    (hmasks : st.masks = ∅) :
    st.correlation S C a N = rowCorrelation S C a N st.shape st.rowFunction := by
  simp [correlation, rowCorrelation, hmasks]

end MaskRemovalState

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
    exact exists_scaleBranch_row_shape Sh Jstar hStar u v huSupp hvSupp hvu
  · have huSupp : u ∈ (Sh.row Sh.star).support := by rw [hStar]; exact huJ
    have hvSupp : v ∈ (Sh.row Sh.star).support := by rw [hStar]; exact hvJ
    exact exists_scaleBalanced_row_shape Sh Jstar hStar u v huSupp hvSupp huv

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
