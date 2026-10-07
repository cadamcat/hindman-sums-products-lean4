import HindmanSumsProducts.Prediction.Outside
import Mathlib.Analysis.MeanInequalities

/-! Helpers for the multi-template dual-product orthogonality proof. -/

namespace HindmanSumsProducts
namespace Prediction

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable


universe u

/-- Finite weighted Cauchy--Schwarz and translation-coordinate bookkeeping, adapted from
`Correlation/PkgElim2.lean` for the dual-test row elimination proof. -/
abbrev pkgB2_ShiftCoord {α : Type u} (E : Finset α) :=
  {x : α × Fin 2 // x.2.val = 0 ∨ x.1 ∈ E}

abbrev pkgB2_ShiftCoordExcept {α : Type u} (E : Finset α) (R : α) :=
  {x : pkgB2_ShiftCoord E // x.val ≠ (R, 0)}

noncomputable def pkgB2_uniformFintypeAverage {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

theorem pkgB2_uniformFintypeAverage_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    pkgB2_uniformFintypeAverage f =
      pkgB2_uniformFintypeAverage (fun x =>
        pkgB2_uniformFintypeAverage (fun y => f (x, y))) := by
  classical
  unfold pkgB2_uniformFintypeAverage
  rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  calc
    _ = (Fintype.card α : ℝ)⁻¹ *
        ((Fintype.card β : ℝ)⁻¹ * ∑ x, ∑ y, f (x, y)) := by
      rw [mul_inv_rev]
      ring
    _ = (Fintype.card α : ℝ)⁻¹ *
        ∑ x, ((Fintype.card β : ℝ)⁻¹ * ∑ y, f (x, y)) := by
      congr 1
      rw [← Finset.mul_sum]

theorem pkgB2_uniformFintypeAverage_sq {α : Type*} [Fintype α]
    (f : α → ℝ) :
    (pkgB2_uniformFintypeAverage f) ^ 2 =
      pkgB2_uniformFintypeAverage (fun p : α × α => f p.1 * f p.2) := by
  classical
  unfold pkgB2_uniformFintypeAverage
  rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Fintype.sum_mul_sum, mul_inv_rev]
  ring

theorem pkgB2_uniformFintypeAverage_const {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) : pkgB2_uniformFintypeAverage (fun _ : α => c) = c := by
  classical
  unfold pkgB2_uniformFintypeAverage
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := α))
  have hsum : (∑ x : α, c) = (Fintype.card α : ℝ) * c := by simp
  rw [hsum]
  field_simp

theorem pkgB2_uniformFintypeAverage_const_mul {α : Type*} [Fintype α]
    (c : ℝ) (f : α → ℝ) :
    pkgB2_uniformFintypeAverage (fun x => c * f x) =
      c * pkgB2_uniformFintypeAverage f := by
  classical
  unfold pkgB2_uniformFintypeAverage
  rw [← Finset.mul_sum]
  ring

noncomputable def pkgB2_shiftStateAverage {α : Type*} [Fintype α]
    [DecidableEq α] (E : Finset α) (L : ℕ)
    (F : (pkgB2_ShiftCoord E → Fin L) → ℝ) : ℝ := by
  classical
  exact pkgB2_uniformFintypeAverage F

noncomputable def pkgB2_shiftCoord_insert_equiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) (hR : R ∉ E) :
    pkgB2_ShiftCoord (insert R E) ≃ pkgB2_ShiftCoord E ⊕ PUnit.{u + 1} := by
  classical
  let extra : pkgB2_ShiftCoord (insert R E) :=
    ⟨(R, 1), Or.inr (Finset.mem_insert_self R E)⟩
  have hcoord (x : pkgB2_ShiftCoord (insert R E))
      (hx : ¬ (x.val.1 = R ∧ x.val.2.val = 1)) :
      x.val.2.val = 0 ∨ x.val.1 ∈ E := by
    rcases x.property with hzero | hxmem
    · exact Or.inl hzero
    · rcases Finset.mem_insert.mp hxmem with heq | hxE
      ·
        have hnotone : x.val.2.val ≠ 1 := by
          intro hone
          exact hx ⟨heq, hone⟩
        have hlt : x.val.2.val < 2 := x.val.2.isLt
        left
        omega
      · exact Or.inr hxE
  let f : pkgB2_ShiftCoord (insert R E) → pkgB2_ShiftCoord E ⊕ PUnit :=
    fun x => if hx : x.val.1 = R ∧ x.val.2.val = 1 then Sum.inr PUnit.unit
      else Sum.inl ⟨x.val, hcoord x hx⟩
  let g : pkgB2_ShiftCoord E ⊕ PUnit → pkgB2_ShiftCoord (insert R E) :=
    fun y => match y with
      | Sum.inl x => ⟨x.val, Or.elim x.property Or.inl (fun hx =>
          Or.inr (Finset.mem_insert_of_mem hx))⟩
      | Sum.inr _ => extra
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    rcases x with ⟨⟨a, b⟩, hp⟩
    apply Subtype.ext
    change (g (f ⟨(a, b), hp⟩)).val = (a, b)
    by_cases hx : a = R ∧ b.val = 1
    · have hb : (1 : Fin 2) = b := (Fin.ext hx.2).symm
      simpa [f, g, hx, extra] using hb
    · simp [f, g, hx, extra]
  · intro y
    cases y with
    | inl x =>
        have hx : ¬ (x.val.1 = R ∧ x.val.2.val = 1) := by
          rintro ⟨hEq, hOne⟩
          rcases x.property with hZero | hxE
          · omega
          · exact hR (hEq ▸ hxE)
        simp [f, g, hx, extra]
    | inr u =>
        cases u
        simp [f, g, extra]

noncomputable def pkgB2_shiftCoord_split_equiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) :
    pkgB2_ShiftCoord E ≃ pkgB2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} := by
  classical
  let point : pkgB2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
  let f : pkgB2_ShiftCoord E → pkgB2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} :=
    fun x => if hx : x.val = (R, 0) then Sum.inr PUnit.unit else
      Sum.inl ⟨x, hx⟩
  let g : pkgB2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} → pkgB2_ShiftCoord E :=
    fun y => match y with
      | Sum.inl x => x.val
      | Sum.inr _ => point
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    by_cases hx : x.val = (R, 0)
    · simp [f, g, hx, point]
    · simp [f, g, hx]
  · intro y
    cases y with
    | inl x =>
        have hx : x.val.val ≠ (R, 0) := x.property
        simp [f, g, hx]
    | inr v =>
        cases v
        simp [f, g, point]

noncomputable def pkgB2_shiftCoordAssignmentSplitEquiv {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (L : ℕ) :
    (pkgB2_ShiftCoord E → Fin L) ≃
      (pkgB2_ShiftCoordExcept E R → Fin L) × Fin L := by
  classical
  let eCoord := pkgB2_shiftCoord_split_equiv E R
  exact (Equiv.arrowCongr eCoord (Equiv.refl (Fin L))).trans
    ((Equiv.sumArrowEquivProdArrow (pkgB2_ShiftCoordExcept E R) PUnit.{u + 1} (Fin L)).trans
      (Equiv.prodCongr (Equiv.refl (pkgB2_ShiftCoordExcept E R → Fin L))
        (Equiv.punitArrowEquiv (Fin L))) )

theorem pkgB2_shiftStateAverage_split {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (L : ℕ)
    (F : (pkgB2_ShiftCoord E → Fin L) → ℝ) :
    pkgB2_shiftStateAverage E L F =
      pkgB2_uniformFintypeAverage (fun v : pkgB2_ShiftCoordExcept E R → Fin L =>
        pkgB2_uniformFintypeAverage (fun t : Fin L =>
          F ((pkgB2_shiftCoordAssignmentSplitEquiv E R L).symm (v, t)))) := by
  classical
  let e := pkgB2_shiftCoordAssignmentSplitEquiv E R L
  have hsum : (∑ x : pkgB2_ShiftCoord E → Fin L, F x) =
      ∑ p : (pkgB2_ShiftCoordExcept E R → Fin L) × Fin L, F (e.symm p) := by
    exact Fintype.sum_equiv e F (fun p => F (e.symm p)) (by intro x; simp)
  have hcard : Fintype.card (pkgB2_ShiftCoord E → Fin L) =
      Fintype.card ((pkgB2_ShiftCoordExcept E R → Fin L) × Fin L) :=
    Fintype.card_congr e
  unfold pkgB2_shiftStateAverage pkgB2_uniformFintypeAverage
  rw [hsum, hcard]
  exact pkgB2_uniformFintypeAverage_prod (fun p => F (e.symm p))

noncomputable def pkgB2_shiftCoordExcept_insert_equiv {α : Type u}
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) :
    pkgB2_ShiftCoordExcept (insert R E) R ≃ pkgB2_ShiftCoord E := by
  classical
  let oldPoint : pkgB2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
  have hcoord (x : pkgB2_ShiftCoordExcept (insert R E) R)
      (hx : x.val.val.1 ≠ R) :
      x.val.val.2.val = 0 ∨ x.val.val.1 ∈ E := by
    rcases x.val.property with hzero | hxmem
    · exact Or.inl hzero
    · rcases Finset.mem_insert.mp hxmem with heq | hxE
      · exact False.elim (hx heq)
      · exact Or.inr hxE
  let f : pkgB2_ShiftCoordExcept (insert R E) R → pkgB2_ShiftCoord E :=
    fun x => if hx : x.val.val.1 = R then oldPoint else ⟨x.val.val, hcoord x hx⟩
  let g : pkgB2_ShiftCoord E → pkgB2_ShiftCoordExcept (insert R E) R :=
    fun x => if hx : x.val.1 = R then
        ⟨⟨(R, 1), Or.inr (Finset.mem_insert_self R E)⟩, by simp⟩
      else ⟨⟨x.val, Or.elim x.property Or.inl (fun hxE =>
        Or.inr (Finset.mem_insert_of_mem hxE))⟩, by
          intro heq
          exact hx (congrArg Prod.fst heq)⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    by_cases hx : x.val.val.1 = R
    · have hb : x.val.val.2.val = 1 := by
        have hne : x.val.val.2.val ≠ 0 := by
          intro hzero
          apply x.property
          apply Prod.ext hx
          exact Fin.ext hzero
        omega
      have hbFin : x.val.val.2 = 1 := Fin.ext hb
      have hgf : g (f x) =
          ⟨⟨(R, 1), Or.inr (Finset.mem_insert_self R E)⟩, by simp⟩ := by
        apply Subtype.ext
        simp [f, g, hx, oldPoint]
      rw [hgf]
      apply Subtype.ext
      apply Subtype.ext
      change (R, 1) = x.val.val
      exact Prod.ext hx.symm hbFin.symm
    · simp [f, g, hx, oldPoint]
  · intro x
    by_cases hx : x.val.1 = R
    · have hzero : x.val.2.val = 0 := by
        rcases x.property with hzero | hxE
        · exact hzero
        · exact False.elim (hR (hx ▸ hxE))
      have hzeroFin : x.val.2 = 0 := Fin.ext hzero
      have hfg : f (g x) = oldPoint := by
        apply Subtype.ext
        simp [f, g, hx, oldPoint]
      rw [hfg]
      apply Subtype.ext
      change (R, 0) = x.val
      exact Prod.ext hx.symm hzeroFin.symm
    · simp [f, g, hx, oldPoint]

noncomputable def pkgB2_shiftStateInsertEquiv {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ) :
    (pkgB2_ShiftCoord (insert R E) → Fin L) ≃
      (pkgB2_ShiftCoord E → Fin L) × Fin L := by
  classical
  let eCoord := pkgB2_shiftCoord_insert_equiv E R hR
  exact (Equiv.arrowCongr eCoord (Equiv.refl (Fin L))).trans
    ((Equiv.sumArrowEquivProdArrow (pkgB2_ShiftCoord E) PUnit.{u + 1} (Fin L)).trans
      (Equiv.prodCongr (Equiv.refl (pkgB2_ShiftCoord E → Fin L))
        (Equiv.punitArrowEquiv (Fin L))) )

theorem pkgB2_shiftStateAverage_insert {α : Type*} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (F : (pkgB2_ShiftCoord (insert R E) → Fin L) → ℝ) :
    pkgB2_shiftStateAverage (insert R E) L F =
      pkgB2_shiftStateAverage E L (fun u =>
        pkgB2_uniformFintypeAverage (fun t : Fin L =>
          F ((pkgB2_shiftStateInsertEquiv E R hR L).symm (u, t)))) := by
  classical
  let e := pkgB2_shiftStateInsertEquiv E R hR L
  have hsum : (∑ u : pkgB2_ShiftCoord (insert R E) → Fin L, F u) =
      ∑ p : (pkgB2_ShiftCoord E → Fin L) × Fin L, F (e.symm p) := by
    exact Fintype.sum_equiv e F (fun p => F (e.symm p)) (by intro u; simp)
  have hcard : Fintype.card (pkgB2_ShiftCoord (insert R E) → Fin L) =
      Fintype.card ((pkgB2_ShiftCoord E → Fin L) × Fin L) :=
    Fintype.card_congr e
  unfold pkgB2_shiftStateAverage pkgB2_uniformFintypeAverage
  rw [hsum, hcard]
  exact pkgB2_uniformFintypeAverage_prod (fun p => F (e.symm p))

abbrev pkgB2_ShiftOutside {α : Type u} (E : Finset α) (R : α) (L : ℕ) :=
  pkgB2_ShiftCoordExcept E R → Fin L

noncomputable def pkgB2_jointStateAverage {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (μ : β → ℝ)
    (L : β → ℕ) (F : ∀ b, (pkgB2_ShiftCoord E → Fin (L b)) → ℝ) : ℝ :=
  ∑ b, μ b * pkgB2_shiftStateAverage E (L b) (F b)

theorem pkgB2_sigma_weighted_uniform_sum {β : Type*} [Fintype β]
    (O : β → Type*) [∀ b, Fintype (O b)] (μ : β → ℝ)
    (F : ∀ b, O b → ℝ) :
    ∑' x : Σ b, O b,
        μ x.1 * (Fintype.card (O x.1) : ℝ)⁻¹ * F x.1 x.2 =
      ∑ b, μ b * pkgB2_uniformFintypeAverage (F b) := by
  classical
  simp only [tsum_fintype, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b hb
  have hs :
      (∑ o : O b, μ b * (Fintype.card (O b) : ℝ)⁻¹ * F b o) =
        μ b * ((Fintype.card (O b) : ℝ)⁻¹ * ∑ o, F b o) := by
    calc
      _ = μ b * (Fintype.card (O b) : ℝ)⁻¹ * ∑ o, F b o := by
        rw [← Finset.mul_sum]
      _ = μ b * ((Fintype.card (O b) : ℝ)⁻¹ * ∑ o, F b o) := by ring
  rw [hs]
  unfold pkgB2_uniformFintypeAverage
  rfl

noncomputable def pkgB2_csCurrentIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (L : β → ℕ)
    (H₀ : ∀ b, pkgB2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, pkgB2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (b : β) (u : pkgB2_ShiftCoord E → Fin (L b)) : ℝ :=
  let e := pkgB2_shiftCoordAssignmentSplitEquiv E R (L b)
  H₀ b (e u).1 * pkgB2_uniformFintypeAverage (H b (e u).1)

noncomputable def pkgB2_csWeightIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (L : β → ℕ)
    (Ω : ∀ b, pkgB2_ShiftOutside E R (L b) → ℝ)
    (b : β) (u : pkgB2_ShiftCoord E → Fin (L b)) : ℝ :=
  Ω b ((pkgB2_shiftCoordAssignmentSplitEquiv E R (L b) u).1)

noncomputable def pkgB2_csNextIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (hR : R ∉ E)
    (L : β → ℕ) (Ω : ∀ b, pkgB2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, pkgB2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (b : β) (u : pkgB2_ShiftCoord (insert R E) → Fin (L b)) : ℝ := by
  classical
  let (v, t₁) := pkgB2_shiftStateInsertEquiv E R hR (L b) u
  let (o, t₀) := pkgB2_shiftCoordAssignmentSplitEquiv E R (L b) v
  exact Ω b o * H b o t₀ * H b o t₁

theorem pkgB2_weightedShiftStateStep {α β : Type u} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (hR : R ∉ E)
    (μ : β → ℝ) (L : β → ℕ) (hL : ∀ b, 0 < L b)
    (H₀ : ∀ b, pkgB2_ShiftOutside E R (L b) → ℝ)
    (Ω : ∀ b, pkgB2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, pkgB2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hΩ : ∀ b o, 0 ≤ Ω b o)
    (h₀ : ∀ b o, |H₀ b o| ≤ Ω b o)
    (hCS : ∀ {γ : Type u} (μ Ω H₀ H₁ : γ → ℝ)
      (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
      (h₀ : ∀ x, |H₀ x| ≤ Ω x)
      (hΩs : Summable (fun x => μ x * Ω x))
      (h₁s : Summable (fun x => μ x * (Ω x * H₁ x ^ 2))),
      |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
        (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2)) :
    |pkgB2_jointStateAverage E μ L
        (pkgB2_csCurrentIntegrand E R L H₀ H)| ^ 2 ≤
      pkgB2_jointStateAverage E μ L (pkgB2_csWeightIntegrand E R L Ω) *
        pkgB2_jointStateAverage (insert R E) μ L
          (pkgB2_csNextIntegrand E R hR L Ω H) := by
  classical
  let Outside : β → Type _ := fun b => pkgB2_ShiftOutside (α := α) E R (L b)
  let γ := Σ b, Outside b
  letI : ∀ b, Fintype (Outside b) := fun b => by
    dsimp [Outside, pkgB2_ShiftOutside]
    infer_instance
  letI : Fintype γ := by
    dsimp [γ]
    infer_instance
  let μ' : γ → ℝ := fun x => μ x.1 * (Fintype.card (Outside x.1) : ℝ)⁻¹
  let Ω' : γ → ℝ := fun x => Ω x.1 x.2
  let H₀' : γ → ℝ := fun x => H₀ x.1 x.2
  let H₁' : γ → ℝ := fun x =>
    pkgB2_uniformFintypeAverage (H x.1 x.2)
  have hμ' : ∀ x, 0 ≤ μ' x := by
    intro x
    exact mul_nonneg (hμ x.1) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hΩ' : ∀ x, 0 ≤ Ω' x := by
    intro x
    exact hΩ x.1 x.2
  have h₀' : ∀ x, |H₀' x| ≤ Ω' x := by
    intro x
    exact h₀ x.1 x.2
  have hΩs : Summable (fun x => μ' x * Ω' x) := by
    exact Summable.of_finite
  have h₁s : Summable (fun x => μ' x * (Ω' x * H₁' x ^ 2)) := by
    exact Summable.of_finite
  have hcs := hCS (γ := γ) μ' Ω' H₀' H₁' hμ' hΩ' h₀' hΩs h₁s
  have hcurrent (b : β) :
      pkgB2_shiftStateAverage E (L b)
        (pkgB2_csCurrentIntegrand E R L H₀ H b) =
      pkgB2_uniformFintypeAverage (fun o : Outside b =>
        H₀ b o * pkgB2_uniformFintypeAverage (H b o)) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    rw [pkgB2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    simp only [pkgB2_csCurrentIntegrand, Equiv.apply_symm_apply]
    apply congrArg (fun f : Outside b → ℝ => pkgB2_uniformFintypeAverage f)
    funext o
    exact pkgB2_uniformFintypeAverage_const
      (H₀ b o * pkgB2_uniformFintypeAverage (H b o))
  have hweight (b : β) :
      pkgB2_shiftStateAverage E (L b)
        (pkgB2_csWeightIntegrand E R L Ω b) =
      pkgB2_uniformFintypeAverage (Ω b) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    rw [pkgB2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    simp only [pkgB2_csWeightIntegrand, Equiv.apply_symm_apply]
    apply congrArg (fun f : Outside b → ℝ => pkgB2_uniformFintypeAverage f)
    funext o
    exact pkgB2_uniformFintypeAverage_const (Ω b o)
  have hnext (b : β) :
      pkgB2_shiftStateAverage (insert R E) (L b)
        (pkgB2_csNextIntegrand E R hR L Ω H b) =
      pkgB2_uniformFintypeAverage (fun o : Outside b =>
        pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          pkgB2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
            Ω b o * H b o t₀ * H b o t₁))) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    let eIns := pkgB2_shiftStateInsertEquiv E R hR (L b)
    let eSplit := pkgB2_shiftCoordAssignmentSplitEquiv E R (L b)
    have hEval (o : Outside b) (t₀ t₁ : Fin (L b)) :
        pkgB2_csNextIntegrand E R hR L Ω H b
          ((pkgB2_shiftStateInsertEquiv E R hR (L b)).symm
            ((pkgB2_shiftCoordAssignmentSplitEquiv E R (L b)).symm (o, t₀), t₁)) =
            Ω b o * H b o t₀ * H b o t₁ := by
      simp [pkgB2_csNextIntegrand]
    rw [pkgB2_shiftStateAverage_insert (E := E) (R := R) (hR := hR) (L := L b)]
    rw [pkgB2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    change pkgB2_uniformFintypeAverage (fun o : Outside b =>
      pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
        pkgB2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
          pkgB2_csNextIntegrand E R hR L Ω H b
            (eIns.symm (eSplit.symm (o, t₀), t₁))))) = _
    apply congrArg (fun f : Outside b → ℝ => pkgB2_uniformFintypeAverage f)
    funext o
    apply congrArg (fun f : Fin (L b) → ℝ => pkgB2_uniformFintypeAverage f)
    funext t₀
    apply congrArg (fun f : Fin (L b) → ℝ => pkgB2_uniformFintypeAverage f)
    funext t₁
    exact hEval o t₀ t₁
  have hleft :
      (∑' x : γ, μ' x * (H₀' x * H₁' x)) =
        pkgB2_jointStateAverage E μ L
          (pkgB2_csCurrentIntegrand E R L H₀ H) := by
    have hsum := pkgB2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => H₀ b o * pkgB2_uniformFintypeAverage (H b o))
    have houter :
        (∑' x : γ, μ' x * (H₀' x * H₁' x)) =
          ∑ b, μ b * pkgB2_uniformFintypeAverage (fun o : Outside b =>
            H₀ b o * pkgB2_uniformFintypeAverage (H b o)) := by
      simpa [μ', H₀', H₁', Outside, mul_assoc] using hsum
    calc
      _ = ∑ b, μ b * pkgB2_uniformFintypeAverage (fun o : Outside b =>
            H₀ b o * pkgB2_uniformFintypeAverage (H b o)) := houter
      _ = _ := by
        unfold pkgB2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hcurrent b]
  have hfirst :
      (∑' x : γ, μ' x * Ω' x) =
        pkgB2_jointStateAverage E μ L (pkgB2_csWeightIntegrand E R L Ω) := by
    have hsum := pkgB2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => Ω b o)
    have houter : (∑' x : γ, μ' x * Ω' x) =
        ∑ b, μ b * pkgB2_uniformFintypeAverage (Ω b) := by
      simpa [μ', Ω', Outside] using hsum
    calc
      _ = ∑ b, μ b * pkgB2_uniformFintypeAverage (Ω b) := houter
      _ = _ := by
        unfold pkgB2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hweight b]
  have hpair (b : β) (o : Outside b) :
      pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
        pkgB2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
          Ω b o * H b o t₀ * H b o t₁)) =
    Ω b o * (pkgB2_uniformFintypeAverage (H b o)) ^ 2 := by
    calc
      _ = pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          (Ω b o * H b o t₀) * pkgB2_uniformFintypeAverage (H b o)) := by
        apply congrArg (fun f : Fin (L b) → ℝ => pkgB2_uniformFintypeAverage f)
        funext t₀
        simpa [mul_assoc] using
          (pkgB2_uniformFintypeAverage_const_mul
            (Ω b o * H b o t₀) (H b o))
      _ = pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          (Ω b o * pkgB2_uniformFintypeAverage (H b o)) * H b o t₀) := by
        apply congrArg (fun f : Fin (L b) → ℝ => pkgB2_uniformFintypeAverage f)
        funext t₀
        ring
      _ = (Ω b o * pkgB2_uniformFintypeAverage (H b o)) *
          pkgB2_uniformFintypeAverage (H b o) :=
        pkgB2_uniformFintypeAverage_const_mul
          (Ω b o * pkgB2_uniformFintypeAverage (H b o)) (H b o)
      _ = _ := by ring
  have hnextReduce (b : β) :
      pkgB2_uniformFintypeAverage (fun o : Outside b =>
        Ω b o * (pkgB2_uniformFintypeAverage (H b o)) ^ 2) =
      pkgB2_shiftStateAverage (insert R E) (L b)
        (pkgB2_csNextIntegrand E R hR L Ω H b) := by
    calc
      _ = pkgB2_uniformFintypeAverage (fun o : Outside b =>
          pkgB2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
            pkgB2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
              Ω b o * H b o t₀ * H b o t₁))) := by
        congr 1
        funext o
        exact (hpair b o).symm
      _ = _ := (hnext b).symm
  have hsecond :
      (∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2)) =
        pkgB2_jointStateAverage (insert R E) μ L
          (pkgB2_csNextIntegrand E R hR L Ω H) := by
    have hsum := pkgB2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => Ω b o * (pkgB2_uniformFintypeAverage (H b o)) ^ 2)
    have houter :
        (∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2)) =
          ∑ b, μ b * pkgB2_uniformFintypeAverage (fun o : Outside b =>
            Ω b o * (pkgB2_uniformFintypeAverage (H b o)) ^ 2) := by
      simpa [μ', Ω', H₁', Outside, mul_assoc] using hsum
    calc
      _ = ∑ b, μ b * pkgB2_uniformFintypeAverage (fun o : Outside b =>
            Ω b o * (pkgB2_uniformFintypeAverage (H b o)) ^ 2) := houter
      _ = _ := by
        unfold pkgB2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hnextReduce b]
  calc
    |pkgB2_jointStateAverage E μ L
        (pkgB2_csCurrentIntegrand E R L H₀ H)| ^ 2 =
        |∑' x : γ, μ' x * (H₀' x * H₁' x)| ^ 2 := by rw [hleft]
    _ ≤ (∑' x : γ, μ' x * Ω' x) *
        ∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2) := hcs
    _ = _ := by rw [hfirst, hsecond]

/-! Row and coordinate indices for several cube templates, with fixed supports. -/

abbrev pkgB2_Nonroot {b : ℕ} (T : Fin b → CubeTemplate) :=
  Σ k : Fin b, {ω : Finset (Fin (T k).d) // ω.Nonempty}

abbrev pkgB2_BaseRow {b : ℕ} (T : Fin b → CubeTemplate) :=
  Unit ⊕ pkgB2_Nonroot T

abbrev pkgB2_OldCoord {b : ℕ} (T : Fin b → CubeTemplate) :=
  Unit ⊕ (Σ k : Fin b, Fin (T k).d × Fin 2)

/-- Extend a direction on a replica to natural shift indices, so response formulas can
compare rows from different dependent dimensions without transporting finsets. -/
def pkgB2_directionLift (d : ℕ) (a : Fin (d + 1) → ℤ) (n : ℕ) : ℤ :=
  if h : n ≤ d then a ⟨n, by omega⟩ else 0

theorem pkgB2_directionLift_zero (d : ℕ) (a : Fin (d + 1) → ℤ) :
    pkgB2_directionLift d a 0 = a 0 := by
  simp [pkgB2_directionLift]

theorem pkgB2_directionLift_succ (d : ℕ) (a : Fin (d + 1) → ℤ)
    (j : Fin d) :
    pkgB2_directionLift d a (j.val + 1) = a j.succ := by
  have hj : j.val + 1 ≤ d := by omega
  simp only [pkgB2_directionLift, dif_pos hj]
  congr 1

theorem pkgB2_directionLift_sum (d : ℕ) (a : Fin (d + 1) → ℤ)
    (ω : Finset (Fin d)) :
    ∑ j ∈ ω, pkgB2_directionLift d a (j.val + 1) = ∑ j ∈ ω, a j.succ := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [pkgB2_directionLift_succ]

/-- Response of the affine form in row `t` to the translation assigned to nonroot row `s`.
The common pivot shift contributes to every row; the upper-shift contribution is present only
inside the selected replica. -/
def pkgB2_response {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (s : pkgB2_Nonroot T) (a : ℕ → ℤ) (t : pkgB2_BaseRow T) : ℤ :=
  match t with
  | .inl _ => a 0 * M s.1
  | .inr r =>
      if h : r.1 = s.1 then
        M s.1 * (a 0 + ∑ j ∈ r.2.1, a (j.val + 1))
      else a 0 * M s.1

theorem pkgB2_response_self {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (s : pkgB2_Nonroot T) (a : ℕ → ℤ)
    (ha : a 0 + ∑ j ∈ s.2.1, a (j.val + 1) = 0) :
    pkgB2_response T M s a (.inr s) = 0 := by
  simp [pkgB2_response, ha]

theorem pkgB2_response_root_ne_zero {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℤ) (s : pkgB2_Nonroot T) (a : ℕ → ℤ)
    (hM : M s.1 ≠ 0) (ha : a 0 ≠ 0) :
    pkgB2_response T M s a (.inl ()) ≠ 0 := by
  simp only [pkgB2_response]
  exact mul_ne_zero ha hM

theorem pkgB2_response_otherReplica_ne_zero {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℤ) (s : pkgB2_Nonroot T) (a : ℕ → ℤ)
    (k : Fin b) (ω : {ω : Finset (Fin (T k).d) // ω.Nonempty})
    (hM : M s.1 ≠ 0) (ha : a 0 ≠ 0) (hk : k ≠ s.1) :
    pkgB2_response T M s a (.inr ⟨k, ω⟩) ≠ 0 := by
  simpa [pkgB2_response, hk] using mul_ne_zero ha hM

theorem pkgB2_response_sameReplica_ne_zero {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℤ) (s : pkgB2_Nonroot T) (a : ℕ → ℤ)
    (ω : {ω : Finset (Fin (T s.1).d) // ω.Nonempty})
    (hM : M s.1 ≠ 0)
    (hsep : ∀ ω' : Finset (Fin (T s.1).d), ω' ≠ s.2.1 →
      a 0 + ∑ j ∈ ω', a (j.val + 1) ≠ 0)
    (hω : ω.1 ≠ s.2.1) :
    pkgB2_response T M s a (.inr ⟨s.1, ω⟩) ≠ 0 := by
  simp only [pkgB2_response]
  exact mul_ne_zero hM (hsep ω.1 hω)

def pkgB2_directionSpec {b : ℕ} (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) : Prop :=
  ∀ r, direction r 0 ≠ 0 ∧
    direction r 0 + ∑ j ∈ r.2.1, direction r j.succ = 0 ∧
    ∀ ω' : Finset (Fin (T r.1).d), ω' ≠ r.2.1 →
      direction r 0 + ∑ j ∈ ω', direction r j.succ ≠ 0

private theorem pkgB2_response_nonzero_of_active {b : ℕ}
    (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hM : ∀ k, M k ≠ 0) (hdir : pkgB2_directionSpec T direction)
    (t : pkgB2_BaseRow T) (r : pkgB2_Nonroot T)
    (hactive : t ≠ Sum.inr r) :
    pkgB2_response T M r (pkgB2_directionLift (T r.1).d (direction r)) t ≠ 0 := by
  cases t with
  | inl _ =>
      exact pkgB2_response_root_ne_zero T M r
        (pkgB2_directionLift (T r.1).d (direction r)) (hM r.1)
        (by simpa [pkgB2_directionLift_zero] using (hdir r).1)
  | inr s =>
      rcases r with ⟨rk, rω⟩
      rcases s with ⟨sk, sω⟩
      have hrowne : (Sum.inr (⟨sk, sω⟩ : pkgB2_Nonroot T) : pkgB2_BaseRow T) ≠
          Sum.inr (⟨rk, rω⟩ : pkgB2_Nonroot T) := hactive
      by_cases hsame : sk = rk
      · subst sk
        have hsubsetne : sω.1 ≠ rω.1 := by
          intro hω
          have hsEq : sω = rω := Subtype.ext hω
          cases hsEq
          exact hrowne rfl
        have hsep : ∀ ω' : Finset (Fin (T rk).d), ω' ≠ rω.1 →
            pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩) 0 +
              ∑ j ∈ ω', pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩)
                (j.val + 1) ≠ 0 := by
          intro ω' hω
          simpa [pkgB2_directionLift_zero, pkgB2_directionLift_sum] using
            (hdir ⟨rk, rω⟩).2.2 ω' hω
        exact pkgB2_response_sameReplica_ne_zero T M ⟨rk, rω⟩
          (pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩)) sω
          (hM rk) hsep hsubsetne
      · exact pkgB2_response_otherReplica_ne_zero T M ⟨rk, rω⟩
          (pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩)) sk sω
          (hM rk)
          (by simpa [pkgB2_directionLift_zero] using (hdir ⟨rk, rω⟩).1)
          hsame

private theorem pkgB2_responseField_nonzero_of_active {b : ℕ} {F : Type*} [Field F]
    (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hM : ∀ k, (M k : F) ≠ 0)
    (hdir0 : ∀ r, (direction r 0 : F) ≠ 0)
    (hdirOther : ∀ r ω', ω' ≠ r.2.1 →
      (direction r 0 : F) + ∑ j ∈ ω', (direction r j.succ : F) ≠ 0)
    (t : pkgB2_BaseRow T) (r : pkgB2_Nonroot T) (hactive : t ≠ Sum.inr r) :
    ((pkgB2_response T M r (pkgB2_directionLift (T r.1).d (direction r)) t : ℤ) : F) ≠ 0 := by
  cases t with
  | inl _ =>
      have hresp : pkgB2_response T M r
          (pkgB2_directionLift (T r.1).d (direction r)) (.inl ()) =
          pkgB2_directionLift (T r.1).d (direction r) 0 * M r.1 := by
        rfl
      rw [hresp, pkgB2_directionLift_zero, Int.cast_mul]
      exact mul_ne_zero (hdir0 r) (hM r.1)
  | inr row =>
      rcases r with ⟨rk, rω⟩
      rcases row with ⟨k, ω⟩
      have hrowne : (Sum.inr (⟨k, ω⟩ : pkgB2_Nonroot T) : pkgB2_BaseRow T) ≠
          Sum.inr (⟨rk, rω⟩ : pkgB2_Nonroot T) := hactive
      by_cases hsame : k = rk
      · subst k
        have hωne : ω.1 ≠ rω.1 := by
          intro hω
          have hsub : ω = rω := Subtype.ext hω
          cases hsub
          exact hrowne rfl
        have hresp : pkgB2_response T M ⟨rk, rω⟩
            (pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩))
            (.inr ⟨rk, ω⟩) =
            M rk * (direction ⟨rk, rω⟩ 0 +
              ∑ j ∈ ω.1, direction ⟨rk, rω⟩ j.succ) := by
          simp [pkgB2_response, pkgB2_directionLift_zero, pkgB2_directionLift_sum]
        rw [hresp, Int.cast_mul, Int.cast_add, Int.cast_sum]
        exact mul_ne_zero (hM rk) (hdirOther ⟨rk, rω⟩ ω.1 hωne)
      · have hresp : pkgB2_response T M ⟨rk, rω⟩
            (pkgB2_directionLift (T rk).d (direction ⟨rk, rω⟩))
            (.inr ⟨k, ω⟩) = direction ⟨rk, rω⟩ 0 * M rk := by
          simp [pkgB2_response, hsame, pkgB2_directionLift_zero]
        rw [hresp, Int.cast_mul]
        exact mul_ne_zero (hdir0 ⟨rk, rω⟩) (hM rk)

def pkgB2_blockScale {K : ℕ} (A : Parameters K) (B : Block K) (N : ℕ) : ℕ :=
  2 + A.M N + ∏ j ∈ B.2.val, (A.X N j) ^ 2

theorem pkgB2_blockScale_le_masterScaleV {K : ℕ} (A : Parameters K)
    (B : Block K) (l : Fin K) (h : ∀ j ∈ B.2.val, j < l) (N : ℕ) :
    pkgB2_blockScale A B N ≤ masterScaleV A N l := by
  unfold pkgB2_blockScale masterScaleV
  apply Nat.add_le_add_left
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h j hj⟩
  · intro j _ _
    exact Nat.one_le_pow _ _ (A.Xpos N j)

/-! Fixed-support copies of each base row after translation directions are inserted. -/

abbrev pkgB2_Copy {R J : Type*} (active : R → J → Prop) (E : Finset J) :=
  Σ r : R, ({j : J // j ∈ E ∧ active r j} → Fin 2)

noncomputable def pkgB2_copyCoeff {R J C F : Type*} [Field F]
    (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (o : pkgB2_Copy active E) : C ⊕ (J × Fin 2) → F := by
  classical
  exact Sum.elim (c o.1) fun js =>
    if h : js.1 ∈ E ∧ active o.1 js.1 then
      if o.2 ⟨js.1, h⟩ = js.2 then ρ o.1 js.1 else 0
    else if js.2 = 0 then ρ o.1 js.1 else 0

noncomputable def pkgB2_copyCoeffInt {R J C : Type*}
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J)
    (o : pkgB2_Copy active E) : C ⊕ (J × Fin 2) → ℤ := by
  classical
  exact Sum.elim (c o.1) fun js =>
    if h : js.1 ∈ E ∧ active o.1 js.1 then
      if o.2 ⟨js.1, h⟩ = js.2 then ρ o.1 js.1 else 0
    else if js.2 = 0 then ρ o.1 js.1 else 0

private theorem pkgB2_copyCoeff_eq_castInt {R J C F : Type*} [Field F]
    (c : R → C → ℤ) (ρ : R → J → ℤ)
    (active : R → J → Prop) (E : Finset J)
    (o : pkgB2_Copy active E) (j : C ⊕ (J × Fin 2)) :
    pkgB2_copyCoeff (fun r a => (c r a : F)) (fun r t => (ρ r t : F))
        active E o j = (pkgB2_copyCoeffInt c ρ active E o j : F) := by
  classical
  cases j with
  | inl c' => rfl
  | inr pair =>
      rcases pair with ⟨t, side⟩
      by_cases h : t ∈ E ∧ active o.1 t
      · by_cases hbit : o.2 ⟨t, h⟩ = side <;>
          simp [pkgB2_copyCoeff, pkgB2_copyCoeffInt, h, hbit]
      · by_cases hs : side = 0 <;>
          simp [pkgB2_copyCoeff, pkgB2_copyCoeffInt, h, hs]

theorem pkgB2_copyCoeff_anchor {R J C F : Type*} [Field F]
    (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (a : C) (ha : ∀ r, c r a = 1) (o : pkgB2_Copy active E) :
    pkgB2_copyCoeff c ρ active E o (.inl a) = 1 := ha o.1

/-- Different base rows separate on an old column; different copies of one row separate
on a branch column. Taking the common anchor as the other column gives a nonzero minor. -/
theorem pkgB2_copies_pairwise_minor {R J C F : Type*} [Field F]
    (c : R → C → F) (ρ : R → J → F)
    (active : R → J → Prop) (E : Finset J)
    (a : C) (ha : ∀ r, c r a = 1)
    (hsep : ∀ r s, r ≠ s → ∃ j, c r j ≠ c s j)
    (hresp : ∀ r j, active r j → ρ r j ≠ 0)
    (o v : pkgB2_Copy active E) (hne : o ≠ v) :
    ∃ j : C ⊕ (J × Fin 2),
      pkgB2_copyCoeff c ρ active E o (.inl a) * pkgB2_copyCoeff c ρ active E v j ≠
        pkgB2_copyCoeff c ρ active E o j * pkgB2_copyCoeff c ρ active E v (.inl a) := by
  classical
  simp only [pkgB2_copyCoeff_anchor c ρ active E a ha, one_mul, mul_one]
  by_cases hrs : o.1 = v.1
  · rcases o with ⟨r, f⟩
    rcases v with ⟨s, g⟩
    simp only at hrs
    subst s
    have hfg : f ≠ g := by
      intro h
      subst g
      exact hne rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfg
    refine ⟨.inr (j.1, f j), ?_⟩
    have hgf : g j ≠ f j := Ne.symm hj
    simpa [pkgB2_copyCoeff, j.2, hgf] using (hresp r j.1 j.2.2).symm
  · obtain ⟨j, hj⟩ := hsep o.1 v.1 hrs
    exact ⟨.inl j, hj.symm⟩

/-! Independent prime replicas are placed in disjoint blocks of the master slots. -/

noncomputable def pkgB2_replicaEmbedding {b sl : ℕ} (k : Fin b) :
    Fin sl ↪ Fin (b * sl) where
  toFun j := finProdFinEquiv (m := b) (n := sl) (k, j)
  inj' := by
    intro i j hij
    have hpair := congrArg (finProdFinEquiv (m := b) (n := sl)).symm hij
    simpa using congrArg Prod.snd hpair

noncomputable def pkgB2_templateEmbedding {sl b : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : Fin b → CubeTemplate} (hT : ∀ k, Allowed Dm (T k)) (k : Fin b) :
    Fin (T k).q ↪ Fin (b * sl) :=
  (Classical.choose (hT k)).trans (pkgB2_replicaEmbedding k)

noncomputable def pkgB2_repTests {sl b : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : Fin b → CubeTemplate} (hT : ∀ k, Allowed Dm (T k)) :
    Finset (IntegerPolynomial (b * sl)) :=
  Finset.univ.image fun k : Fin b =>
    MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D

theorem pkgB2_templateModulus_mem {sl b : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : Fin b → CubeTemplate} (hT : ∀ k, Allowed Dm (T k)) (k : Fin b) :
    MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D ∈
      pkgB2_repTests hT := by
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

noncomputable def pkgB2_repGap {K b sl : ℕ} (gap : Fin b → Fin K) :
    Fin (b * sl) → Fin K :=
  fun t => gap ((finProdFinEquiv (m := b) (n := sl)).symm t).1

noncomputable def pkgB2_repPrimeProject {sl b : ℕ} {Dm : Finset (IntegerPolynomial sl)}
    {T : Fin b → CubeTemplate} (hT : ∀ k, Allowed Dm (T k))
    (p : Fin (b * sl) → ℕ) (k : Fin b) : Fin (T k).q → ℕ :=
  fun j => p (pkgB2_templateEmbedding hT k j)

noncomputable def pkgB2_repScalesOfFacts {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (hUniform : Tendsto
      (fun N : ℕ => uniformUnitTupleProbability ((primorial (N + 1)) ^ MS.primeStage.e0 N)
        (b * sl) (uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
          (MS.primeStage.e0 N))) atTop (𝓝 0))
    (hActual : ∀ l, Tendsto
      (fun N : ℕ => independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N)))
      atTop (𝓝 0))
    (hZero : ∀ l, SuperPolynomialSmall
      (fun N => independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (polynomialZeroOrRepeated (pkgB2_repTests hT)))
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)))
    (hDvd : ∀ N l (p : Fin (b * sl) → ℕ) (Q : IntegerPolynomial (b * sl)),
      Q ∈ pkgB2_repTests hT →
      (∀ i, (MS.primeStage.pool N l).lower ≤ p i ∧
        p i < (MS.primeStage.pool N l).upper ∧ (p i).Prime) →
      evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0 →
      MS.core.parameters.M N *
        (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∣
          MS.core.parameters.H N l) :
    MasterScales K As (b * sl) (pkgB2_repTests hT) := by
  classical
  refine
    { core := MS.core
      primeStage :=
        { e0 := MS.primeStage.e0
          pool := MS.primeStage.pool
          e0_pos := MS.primeStage.e0_pos
          uniform_small_prime_exception := hUniform
          pool_lower_dominates := MS.primeStage.pool_lower_dominates
          pool_harmonic_mass_dominates := MS.primeStage.pool_harmonic_mass_dominates
          pool_residue_error := MS.primeStage.pool_residue_error
          actual_small_prime_exception := hActual
          zero_and_repeat_probability := hZero }
      gapStage := ?_ }
  exact
    { gap_dominates_pool_and_bound := MS.gapStage.gap_dominates_pool_and_bound
      gap_modulus_divides := MS.gapStage.gap_modulus_divides
      earlier_gaps_divide := MS.gapStage.earlier_gaps_divide
      polynomial_values_divide_gap := hDvd
      raw_cutoff_log_dominates_gap := MS.gapStage.raw_cutoff_log_dominates_gap
      coefficient_divides_modulus := MS.gapStage.coefficient_divides_modulus
      valid_raw_cutoffs := MS.gapStage.valid_raw_cutoffs }

private noncomputable def pkgB2_slotRangeEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    Fin q ≃ {j : Fin s // j ∈ Set.range ι} where
  toFun i := ⟨ι i, ⟨i, rfl⟩⟩
  invFun j := Classical.choose j.2
  left_inv := by
    intro i
    apply ι.injective
    exact Classical.choose_spec (⟨i, rfl⟩ : ι i ∈ Set.range ι)
  right_inv := by
    intro j
    apply Subtype.ext
    exact Classical.choose_spec j.2

private noncomputable def pkgB2_slotIndexEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    (Fin q ⊕ {j : Fin s // j ∉ Set.range ι}) ≃ Fin s :=
  (Equiv.sumCongr (pkgB2_slotRangeEquiv ι) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range ι))

@[simp] private theorem pkgB2_slotIndexEquiv_inl {q s : ℕ} (ι : Fin q ↪ Fin s)
    (i : Fin q) : pkgB2_slotIndexEquiv ι (Sum.inl i) = ι i := by
  change (pkgB2_slotRangeEquiv ι i).1 = ι i
  rfl

@[simp] private theorem pkgB2_slotIndexEquiv_inr {q s : ℕ} (ι : Fin q ↪ Fin s)
    (j : {j : Fin s // j ∉ Set.range ι}) : pkgB2_slotIndexEquiv ι (Sum.inr j) = j.1 := by
  change j.1 = j.1
  rfl

private noncomputable def pkgB2_slotTupleSplit {q s : ℕ} (ι : Fin q ↪ Fin s) (A : Type*) :
    (Fin s → A) ≃ ((Fin q → A) × ({j : Fin s // j ∉ Set.range ι} → A)) :=
  (Equiv.arrowCongr (pkgB2_slotIndexEquiv ι).symm (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow (Fin q) {j : Fin s // j ∉ Set.range ι} A)

@[simp] private theorem pkgB2_slotTupleSplit_left {q s : ℕ} (ι : Fin q ↪ Fin s)
    (A : Type*) (p : Fin s → A) (i : Fin q) :
    (pkgB2_slotTupleSplit ι A p).1 i = p (ι i) := by
  simp [pkgB2_slotTupleSplit, pkgB2_slotIndexEquiv_inl]

@[simp] private theorem pkgB2_slotTupleSplit_right {q s : ℕ} (ι : Fin q ↪ Fin s)
    (A : Type*) (p : Fin s → A) (j : {j : Fin s // j ∉ Set.range ι}) :
    (pkgB2_slotTupleSplit ι A p).2 j = p j.1 := by
  simp [pkgB2_slotTupleSplit, pkgB2_slotIndexEquiv_inr]

private theorem pkgB2_slotTupleSplit_symm_left {q s : ℕ} (ι : Fin q ↪ Fin s)
    (A : Type*) (p : (Fin q → A) × ({j : Fin s // j ∉ Set.range ι} → A))
    (i : Fin q) : (pkgB2_slotTupleSplit ι A).symm p (ι i) = p.1 i := by
  calc
    (pkgB2_slotTupleSplit ι A).symm p (ι i) =
        ((pkgB2_slotTupleSplit ι A) ((pkgB2_slotTupleSplit ι A).symm p)).1 i := by
          rw [pkgB2_slotTupleSplit_left]
    _ = p.1 i := congrFun (congrArg Prod.fst
      ((pkgB2_slotTupleSplit ι A).apply_symm_apply p)) i

private theorem pkgB2_slotTupleSplit_symm_right {q s : ℕ} (ι : Fin q ↪ Fin s)
    (A : Type*) (p : (Fin q → A) × ({j : Fin s // j ∉ Set.range ι} → A))
    (j : {j : Fin s // j ∉ Set.range ι}) :
    (pkgB2_slotTupleSplit ι A).symm p j.1 = p.2 j := by
  calc
    (pkgB2_slotTupleSplit ι A).symm p j.1 =
        ((pkgB2_slotTupleSplit ι A) ((pkgB2_slotTupleSplit ι A).symm p)).2 j := by
          rw [pkgB2_slotTupleSplit_right]
    _ = p.2 j := congrFun (congrArg Prod.snd
      ((pkgB2_slotTupleSplit ι A).apply_symm_apply p)) j

private theorem pkgB2_uniformUnitTupleMass_prod {Q m : ℕ} (x : Fin m → Fin Q) :
    uniformUnitTupleMass Q m x = ∏ i, uniformUnitResidueLaw Q (x i) := by
  classical
  by_cases hall : ∀ i : Fin m, Nat.Coprime (x i).val Q
  · have hprod :
      (∏ i, uniformUnitResidueLaw Q (x i)) = 1 / (Nat.totient Q : ℝ) ^ m := by
      calc
        _ = ∏ i : Fin m, (1 / (Nat.totient Q : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [uniformUnitResidueLaw, hall i]
        _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
    simp [uniformUnitTupleMass, hall, hprod]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hprod : ∏ j, uniformUnitResidueLaw Q (x j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [uniformUnitResidueLaw, hi]
    simp [uniformUnitTupleMass, hall, hprod]

private theorem pkgB2_uniformUnitTupleProbability_prod {Q m : ℕ}
    (E : (Fin m → Fin Q) → Prop) :
    uniformUnitTupleProbability Q m E =
      ∑ x : Fin m → Fin Q,
        (∏ i, uniformUnitResidueLaw Q (x i)) * (if E x then 1 else 0) := by
  classical
  unfold uniformUnitTupleProbability
  apply Finset.sum_congr rfl
  intro x hx
  rw [pkgB2_uniformUnitTupleMass_prod]

theorem pkgB2_uniformUnitTupleProbability_iid_marginal {q s Q : ℕ}
    (hQ : 0 < Q) (ι : Fin q ↪ Fin s) (E : (Fin q → Fin Q) → Prop) :
    uniformUnitTupleProbability Q s (fun x => E (fun i => x (ι i))) =
      uniformUnitTupleProbability Q q E := by
  classical
  let C := {j : Fin s // j ∉ Set.range ι}
  let e := pkgB2_slotTupleSplit ι (Fin Q)
  let μ : Fin Q → ℝ := uniformUnitResidueLaw Q
  have hctotal : ∑ z : C → Fin Q, ∏ j, μ (z j) = 1 := by
    calc
      _ = ∏ j : C, ∑ a : Fin Q, μ a := by
        symm
        exact Fintype.prod_sum (fun (_ : C) (a : Fin Q) => μ a)
      _ = 1 := by simp [μ, uniformUnitResidueLaw_sum_one hQ]
  have hsum :
      (∑ x : Fin s → Fin Q,
          (∏ i, μ (x i)) * (if E (fun i => x (ι i)) then 1 else 0)) =
        ∑ y : (Fin q → Fin Q) × (C → Fin Q),
          (∏ i, μ (e.symm y i)) * (if E y.1 then 1 else 0) := by
    apply Fintype.sum_equiv e
    intro x
    have hleft : (e x).1 = (fun i => x (ι i)) := by
      funext i
      exact pkgB2_slotTupleSplit_left ι (Fin Q) x i
    rw [hleft]
    simp [e]
  have hmass (y : (Fin q → Fin Q) × (C → Fin Q)) :
      (∏ i : Fin s, μ (e.symm y i)) =
        (∏ i : Fin q, μ (y.1 i)) * (∏ j : C, μ (y.2 j)) := by
    calc
      (∏ i : Fin s, μ (e.symm y i)) =
          ∏ t : Fin q ⊕ C, μ (e.symm y (pkgB2_slotIndexEquiv ι t)) := by
        symm
        exact Fintype.prod_equiv (pkgB2_slotIndexEquiv ι)
          (fun t => μ (e.symm y (pkgB2_slotIndexEquiv ι t)))
          (fun i => μ (e.symm y i)) (by intro t; rfl)
      _ = (∏ i : Fin q, μ (e.symm y (ι i))) *
          ∏ j : C, μ (e.symm y j.1) := by
        rw [Fintype.prod_sum_type]
        congr 1
      _ = (∏ i : Fin q, μ (y.1 i)) * ∏ j : C, μ (y.2 j) := by
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          rw [pkgB2_slotTupleSplit_symm_left]
        · apply Finset.prod_congr rfl
          intro j hj
          rw [pkgB2_slotTupleSplit_symm_right]
  have hsum' :
      (∑ y : (Fin q → Fin Q) × (C → Fin Q),
          (∏ i, μ (e.symm y i)) * (if E y.1 then 1 else 0)) =
        ∑ x : Fin q → Fin Q,
          (∏ i, μ (x i)) * (if E x then 1 else 0) := by
    simp_rw [hmass]
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x : Fin q → Fin Q,
          ((∏ i, μ (x i)) * (if E x then 1 else 0)) *
            ∑ z : C → Fin Q, ∏ j, μ (z j) := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          _ = ∑ z : C → Fin Q,
              ((∏ i, μ (x i)) * (if E x then 1 else 0)) * (∏ j, μ (z j)) := by
                apply Finset.sum_congr rfl
                intro z hz
                ring
          _ = _ := by rw [← Finset.mul_sum]
      _ = ∑ x : Fin q → Fin Q,
          (∏ i, μ (x i)) * (if E x then 1 else 0) := by simp [hctotal]
  calc
    uniformUnitTupleProbability Q s (fun x => E (fun i => x (ι i))) =
        ∑ x : Fin s → Fin Q,
          (∏ i, μ (x i)) * (if E (fun i => x (ι i)) then 1 else 0) := by
            rw [pkgB2_uniformUnitTupleProbability_prod]
    _ = ∑ y : (Fin q → Fin Q) × (C → Fin Q),
          (∏ i, μ (e.symm y i)) * (if E y.1 then 1 else 0) := hsum
    _ = ∑ x : Fin q → Fin Q,
          (∏ i, μ (x i)) * (if E x then 1 else 0) := hsum'
    _ = uniformUnitTupleProbability Q q E := by
          symm
          rw [pkgB2_uniformUnitTupleProbability_prod]

private noncomputable def pkgB2_poolRangeTupleEquiv {m M : ℕ} :
    {p : Fin m → ℕ // p ∈ Fintype.piFinset (fun _ : Fin m => Finset.range M)} ≃
      (Fin m → Fin M) where
  toFun p i := ⟨p.1 i, by
    have hi := Fintype.mem_piFinset.mp p.2 i
    exact Finset.mem_range.mp hi⟩
  invFun p := ⟨fun i => (p i).val, Fintype.mem_piFinset.mpr (fun i =>
    Finset.mem_range.mpr (p i).isLt)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro p
    funext i
    apply Fin.ext
    rfl

/-- Finite-range form of an independent prime-pool event. A common finite upper bound for
the slot cutoffs makes the sum a finite product average, even when slot ranges differ. -/
private theorem pkgB2_independentPrimePoolProbability_finite {m : ℕ}
    (lo hi : Fin m → ℕ) (M : ℕ) (hhi : ∀ i, hi i ≤ M)
    (E : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability lo hi E =
      ∑ p : Fin m → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if E (fun i => (p i).val) then 1 else 0) := by
  classical
  let S : Finset (Fin m → ℕ) := Fintype.piFinset
    (fun _ : Fin m => Finset.range M)
  have htermZero (p : Fin m → ℕ) (hp : p ∉ S) :
      independentPrimePoolMass lo hi p * (if E p then 1 else 0) = 0 := by
    have hnot : ¬ ∀ i : Fin m, p i ∈ Finset.range M := by
      intro hall
      apply hp
      simpa [S, Fintype.mem_piFinset] using hall
    obtain ⟨i, hiMem⟩ := not_forall.mp hnot
    have hmass : independentPrimePoolMass lo hi p = 0 := by
      unfold independentPrimePoolMass
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      unfold primePoolLaw
      split_ifs with h
      · exact False.elim (hiMem (Finset.mem_range.mpr (lt_of_lt_of_le h.2.1 (hhi i))))
      · rfl
    simp [hmass]
  have hsum : independentPrimePoolProbability lo hi E =
      ∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then 1 else 0) := by
    unfold independentPrimePoolProbability
    exact tsum_eq_sum (s := S) htermZero
  have hattach :
      (∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then 1 else 0)) =
        ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then 1 else 0) := by
    rw [← Finset.sum_attach]
    simp
  calc
    independentPrimePoolProbability lo hi E =
        ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then 1 else 0) := by
            rw [hsum, hattach]
    _ = ∑ p : Fin m → Fin M,
          (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
            (if E (fun i => (p i).val) then 1 else 0) := by
          apply Fintype.sum_equiv (pkgB2_poolRangeTupleEquiv (m := m) (M := M))
          intro p
          have hval :
              (fun i => ((pkgB2_poolRangeTupleEquiv (m := m) (M := M) p) i).val) = p.1 := by
            funext i
            rfl
          simp only [independentPrimePoolMass]
          rw [← hval]

private noncomputable def pkgB2_blockTupleEquiv {b sl M : ℕ} :
    (Fin (b * sl) → Fin M) ≃ (Fin b → Fin sl → Fin M) where
  toFun p k j := p (pkgB2_replicaEmbedding k j)
  invFun p i := p ((finProdFinEquiv (m := b) (n := sl)).symm i).1
      ((finProdFinEquiv (m := b) (n := sl)).symm i).2
  left_inv := by
    intro p
    funext i
    exact congrArg p ((finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i)
  right_inv := by
    intro p
    funext k j
    exact congrArg (fun z : Fin b × Fin sl => p z.1 z.2)
      ((finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j))

/-- Independent prime slots factor across disjoint replica blocks, even when each block has a
different pool. -/
private theorem pkgB2_independentPrimePoolProbability_blockFactor {b sl M : ℕ}
    (lo hi : Fin (b * sl) → ℕ) (loBlock hiBlock : Fin b → ℕ)
    (hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k)
    (hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k)
    (hbound : (∀ i, hi i ≤ M) ∧ ∀ k, hiBlock k ≤ M)
    (G : ∀ k : Fin b, (Fin sl → ℕ) → Prop) :
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) =
      ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
        (fun _ => hiBlock k) (fun p => G k p) := by
  classical
  let Btuple := pkgB2_blockTupleEquiv (b := b) (sl := sl) (M := M)
  let term : ∀ k, (Fin sl → Fin M) → ℝ := fun k q =>
    (∏ j, primePoolLaw (loBlock k) (hiBlock k) (q j).val) *
      (if G k (fun j => (q j).val) then 1 else 0)
  have hfinite := pkgB2_independentPrimePoolProbability_finite lo hi M hbound.1
    (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j)))
  have hmass (p : Fin (b * sl) → Fin M) :
      independentPrimePoolMass lo hi (fun i => (p i).val) =
        ∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
          (p (pkgB2_replicaEmbedding k j)).val := by
    unfold independentPrimePoolMass
    calc
      ∏ i : Fin (b * sl), primePoolLaw (lo i) (hi i) (p i).val =
          ∏ z : Fin b × Fin sl,
            primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
              (hi (finProdFinEquiv (m := b) (n := sl) z))
              (p (finProdFinEquiv (m := b) (n := sl) z)).val := by
                symm
                exact Fintype.prod_equiv (finProdFinEquiv (m := b) (n := sl))
                  (fun z => primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
                    (hi (finProdFinEquiv (m := b) (n := sl) z))
                    (p (finProdFinEquiv (m := b) (n := sl) z)).val)
                  (fun i => primePoolLaw (lo i) (hi i) (p i).val) (by intro z; rfl)
      _ = ∏ k : Fin b, ∏ j : Fin sl,
            primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val := by
                rw [Fintype.prod_prod_type]
                apply Finset.prod_congr rfl
                intro k hk
                apply Finset.prod_congr rfl
                intro j hj
                have hlo' : lo (finProdFinEquiv (m := b) (n := sl) (k, j)) = loBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hlo k j
                have hhi' : hi (finProdFinEquiv (m := b) (n := sl) (k, j)) = hiBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hhi k j
                rw [hlo', hhi']
                rfl
  have hterm (p : Fin (b * sl) → Fin M) :
      (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) =
        ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
    have hEvent :
        (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then (1 : ℝ) else 0) =
          ∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then (1 : ℝ) else 0 := by
      by_cases hall : ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val)
      · simp [hall]
      · obtain ⟨k, hk⟩ := not_forall.mp hall
        have hzero : ∏ k' : Fin b,
            (if G k' (fun j => (p (pkgB2_replicaEmbedding k' j)).val) then (1 : ℝ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
        simpa only [if_neg hall] using hzero.symm
    calc
      _ = independentPrimePoolMass lo hi (fun i => (p i).val) *
            (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
              rfl
      _ = (∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val) *
            (∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
              rw [hmass p]
              exact congrArg (fun z : ℝ =>
                (∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
                  (p (pkgB2_replicaEmbedding k j)).val) * z) hEvent
      _ = ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
              simp only [term]
              rw [← Finset.prod_mul_distrib]
  have hfactor :
    (∑ p : Fin (b * sl) → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0)) =
        ∏ k, ∑ q : Fin sl → Fin M, term k q := by
    calc
      _ = ∑ q : Fin b → Fin sl → Fin M, ∏ k, term k (q k) := by
        apply Fintype.sum_equiv Btuple
        intro p
        have hB (k : Fin b) : Btuple p k =
            fun j => p (pkgB2_replicaEmbedding k j) := rfl
        simpa only [hB] using hterm p
      _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := by
        symm
        exact Fintype.prod_sum (fun k q => term k q)
  have hRHS (k : Fin b) :
      independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (fun p => G k p) =
        ∑ q : Fin sl → Fin M, term k q := by
    simpa [term, independentPrimePoolMass] using
      (pkgB2_independentPrimePoolProbability_finite
        (fun _ : Fin sl => loBlock k) (fun _ => hiBlock k) M
        (fun _ => hbound.2 k) (G k))
  calc
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) =
      ∑ p : Fin (b * sl) → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
            simpa using hfinite
    _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := hfactor
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (fun p => G k p) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact (hRHS k).symm

private theorem pkgB2_repGoodProbability_eq_product {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (hsl : 0 < sl) (N : ℕ)
    (hpool : ∀ k, 0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
      (MS.primeStage.pool N (gap k)).upper) :
    independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      ∏ k, gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let loBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).lower
  let hiBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).upper
  let G : ∀ k : Fin b, (Fin sl → ℕ) → Prop := fun k q =>
    (T k).Good (corrScales MS) (gap k) N
      (fun j => q ((Classical.choose (hT k)) j))
  have hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).lower = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).upper = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  let M := ∑ i : Fin (b * sl), hi i
  have hboundFull : ∀ i, hi i ≤ M := by
    intro i
    dsimp [M]
    exact Finset.single_le_sum (fun j hj => Nat.zero_le (hi j)) (Finset.mem_univ i)
  have hboundBlock : ∀ k, hiBlock k ≤ M := by
    intro k
    let j0 : Fin sl := ⟨0, hsl⟩
    rw [← hhi k j0]
    exact hboundFull (pkgB2_replicaEmbedding k j0)
  have hproject (p : Fin (b * sl) → ℕ) (k : Fin b) :
      pkgB2_repPrimeProject hT p k =
        fun j => p (pkgB2_replicaEmbedding k ((Classical.choose (hT k)) j)) := by
    funext j
    rfl
  have hfullEvent :
      (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
        (pkgB2_repPrimeProject hT p k)) =
      (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
    funext p
    apply propext
    apply forall_congr'
    intro k
    rw [hproject p k]
  have hfactor := pkgB2_independentPrimePoolProbability_blockFactor
    lo hi loBlock hiBlock hlo hhi ⟨hboundFull, hboundBlock⟩ G
  have hmarginal (k : Fin b) :
      independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) =
        gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
    have h := independentPrimePoolProbability_iid_marginal
      (loBlock k) (hiBlock k) (hpool k) (Classical.choose (hT k))
      ((T k).Good (corrScales MS) (gap k) N)
    simpa [G, loBlock, hiBlock, gapSlotProbability, corrScales] using h.symm
  calc
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
          rw [hfullEvent]
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) := hfactor
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      exact hmarginal k

private theorem pkgB2_repGoodProbability_lower_eventually {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (hsl : 0 < sl) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) ^ b ≤ independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) := by
  have hgood (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have hlim := good_probability_tendsto_one MS (T k) (hT k) (gap k)
    exact hlim.eventually (Ioi_mem_nhds (by norm_num))
  have hpoolPos (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have hratio := MS.primeStage.pool_harmonic_mass_dominates (gap k) 1 (by norm_num)
    have hlarge : ∀ᶠ N : ℕ in atTop,
        1 ≤ primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper /
            (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      simpa [pow_one] using hratio.eventually_ge_atTop (1 : ℝ)
    filter_upwards [hlarge] with N hN
    have hVpos : 0 < (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      unfold masterScaleV
      positivity
    have hmass := (le_div_iff₀ hVpos).mp hN
    have hmassPos :
        0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper := by
      linarith
    exact hmassPos
  have hgoodAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hgood k)
    simpa using h
  have hpoolAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hpoolPos k)
    simpa using h
  filter_upwards [hgoodAll, hpoolAll] with N hgoodN hpoolN
  have hfactor := pkgB2_repGoodProbability_eq_product MS gap T hT hsl N hpoolN
  rw [hfactor]
  calc
    (1 / 2 : ℝ) ^ b = ∏ k : Fin b, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ k : Fin b, gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
        apply Finset.prod_le_prod₀
        · intro k hk
          norm_num
        · intro k hk
          exact le_of_lt (hgoodN k)

theorem pkgB2_uniformUnitTupleProbability_exists_le {α : Type*} {Q m : ℕ}
    (s : Finset α) (E : α → (Fin m → Fin Q) → Prop) :
    uniformUnitTupleProbability Q m (fun x => ∃ a ∈ s, E a x) ≤
      ∑ a ∈ s, uniformUnitTupleProbability Q m (E a) := by
  classical
  unfold uniformUnitTupleProbability
  have hmass (x : Fin m → Fin Q) : 0 ≤ uniformUnitTupleMass Q m x := by
    unfold uniformUnitTupleMass
    split_ifs <;> positivity
  calc
    _ ≤ ∑ x : Fin m → Fin Q,
        uniformUnitTupleMass Q m x * (∑ a ∈ s, if E a x then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hmass x)
      by_cases hevent : (fun x => ∃ a ∈ s, E a x) x
      · let hkeep := hevent
        obtain ⟨a, ha, hE⟩ := hevent
        have hterm : (if E a x then (1 : ℝ) else 0) = 1 := if_pos hE
        have hsum : (1 : ℝ) ≤ ∑ a ∈ s, if E a x then (1 : ℝ) else 0 := by
          have hnonneg : ∀ a ∈ s, 0 ≤ (if E a x then (1 : ℝ) else 0) := by
            intro a ha
            split_ifs <;> norm_num
          calc
            1 = if E a x then (1 : ℝ) else 0 := hterm.symm
            _ ≤ ∑ a ∈ s, if E a x then (1 : ℝ) else 0 :=
              Finset.single_le_sum hnonneg ha
        simpa only [if_pos hkeep] using hsum
      · have hzero : ∀ a ∈ s, ¬ E a x := by
          intro a ha hE
          exact hevent ⟨a, ha, hE⟩
        simp only [if_neg hevent]
        apply Finset.sum_nonneg
        intro a ha
        simp [hzero a ha]
    _ = ∑ a ∈ s, ∑ x : Fin m → Fin Q,
        uniformUnitTupleMass Q m x * (if E a x then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]

theorem pkgB2_independentPrimePoolProbability_exists_le {α : Type*} {m : ℕ}
    (lo hi : Fin m → ℕ) (s : Finset α) (E : α → (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability lo hi (fun p => ∃ a ∈ s, E a p) ≤
      ∑ a ∈ s, independentPrimePoolProbability lo hi (E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [independentPrimePoolProbability]
  | @insert a s ha ih =>
      have heq :
          (fun p => ∃ t ∈ insert a s, E t p) =
            fun p => E a p ∨ ∃ t ∈ s, E t p := by
        funext p
        apply propext
        simp [Finset.mem_insert, ha]
      rw [heq]
      calc
        independentPrimePoolProbability lo hi (fun p => E a p ∨ ∃ t ∈ s, E t p) ≤
            independentPrimePoolProbability lo hi (E a) +
              independentPrimePoolProbability lo hi (fun p => ∃ t ∈ s, E t p) :=
          independentPrimePoolProbability_union_le lo hi (E a) (fun p => ∃ t ∈ s, E t p)
        _ ≤ independentPrimePoolProbability lo hi (E a) +
              ∑ t ∈ s, independentPrimePoolProbability lo hi (E t) :=
          by
            simpa [add_comm] using
              (add_le_add_right ih (independentPrimePoolProbability lo hi (E a)))
        _ = ∑ t ∈ insert a s, independentPrimePoolProbability lo hi (E t) := by
          rw [Finset.sum_insert ha]

theorem pkgB2_renameEval {q m : ℕ} (ι : Fin q ↪ Fin m)
    (P : IntegerPolynomial q) (p : Fin m → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun j => (p (ι j) : ℤ)) := by
  unfold evalIntegerPolynomial
  rw [MvPolynomial.eval_rename]
  rfl

theorem pkgB2_uniformUnitTupleProbability_mono {Q m : ℕ}
    {E F : (Fin m → Fin Q) → Prop} (hEF : ∀ x, E x → F x) :
    uniformUnitTupleProbability Q m E ≤ uniformUnitTupleProbability Q m F := by
  classical
  unfold uniformUnitTupleProbability
  apply Finset.sum_le_sum
  intro x hx
  have hmass : 0 ≤ uniformUnitTupleMass Q m x := by
    unfold uniformUnitTupleMass
    split_ifs <;> positivity
  by_cases hE : E x
  · have hF : F x := hEF x hE
    simp [hE, hF]
  · by_cases hF : F x
    · simpa [hE, hF] using hmass
    · simp [hE, hF]

theorem pkgB2_uniformUnitTupleProbability_nonneg {Q m : ℕ}
    (E : (Fin m → Fin Q) → Prop) :
    0 ≤ uniformUnitTupleProbability Q m E := by
  classical
  unfold uniformUnitTupleProbability
  apply Finset.sum_nonneg
  intro x hx
  unfold uniformUnitTupleMass
  split_ifs <;> positivity

theorem pkgB2_repUniformSmallException_subset {sl b : ℕ}
    {Dm : Finset (IntegerPolynomial sl)} {T : Fin b → CubeTemplate}
    (hT : ∀ k, Allowed Dm (T k)) (w e : ℕ)
    (p : Fin (b * sl) → Fin ((primorial w) ^ e))
    (hbad : uniformSmallPrimeException (pkgB2_repTests hT) w e p) :
    ∃ k : Fin b,
      uniformSmallPrimeException Dm w e (fun j => p (pkgB2_replicaEmbedding k j)) := by
  classical
  rcases hbad with ⟨π, hπ, hπw, Q, hQ, hdiv⟩
  rcases Finset.mem_image.mp hQ with ⟨k, hk, rfl⟩
  let ι : Fin (T k).q ↪ Fin sl := Classical.choose (hT k)
  let pblock : Fin sl → Fin ((primorial w) ^ e) :=
    fun j => p (pkgB2_replicaEmbedding k j)
  have hlisted : MvPolynomial.rename ι (T k).D ∈ Dm :=
    (Classical.choose_spec (hT k)) (T k).D (T k).D_mem
  have hEval :
      evalIntegerPolynomial
          (MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D)
          (fun i => ((p i).val : ℤ)) =
        evalIntegerPolynomial (MvPolynomial.rename ι (T k).D)
          (fun j => ((pblock j).val : ℤ)) := by
    rw [pkgB2_renameEval (pkgB2_templateEmbedding hT k) (T k).D
      (fun i => (p i).val)]
    rw [pkgB2_renameEval ι (T k).D (fun j => (pblock j).val)]
    rfl
  refine ⟨k, π, hπ, hπw, MvPolynomial.rename ι (T k).D, hlisted, ?_⟩
  simpa [hEval] using hdiv

theorem pkgB2_repActualSmallException_subset {sl b : ℕ}
    {Dm : Finset (IntegerPolynomial sl)} {T : Fin b → CubeTemplate}
    (hT : ∀ k, Allowed Dm (T k)) (w e : ℕ)
    (p : Fin (b * sl) → ℕ)
    (hbad : primeSmallDivisibilityEvent (pkgB2_repTests hT) w e p) :
    ∃ k : Fin b,
      primeSmallDivisibilityEvent Dm w e (fun j => p (pkgB2_replicaEmbedding k j)) := by
  classical
  rcases hbad with ⟨π, hπ, hπw, Q, hQ, hdiv⟩
  rcases Finset.mem_image.mp hQ with ⟨k, hk, rfl⟩
  let ι : Fin (T k).q ↪ Fin sl := Classical.choose (hT k)
  let pblock : Fin sl → ℕ := fun j => p (pkgB2_replicaEmbedding k j)
  have hlisted : MvPolynomial.rename ι (T k).D ∈ Dm :=
    (Classical.choose_spec (hT k)) (T k).D (T k).D_mem
  have hEval :
      evalIntegerPolynomial
          (MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D)
          (fun i => (p i : ℤ)) =
        evalIntegerPolynomial (MvPolynomial.rename ι (T k).D)
          (fun j => (pblock j : ℤ)) := by
    rw [pkgB2_renameEval (pkgB2_templateEmbedding hT k) (T k).D p]
    rw [pkgB2_renameEval ι (T k).D pblock]
    rfl
  refine ⟨k, π, hπ, hπw, MvPolynomial.rename ι (T k).D, hlisted, ?_⟩
  simpa [hEval] using hdiv

theorem pkgB2_repUniformSmallException_probability_bound {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) :
    uniformUnitTupleProbability ((primorial (N + 1)) ^ MS.primeStage.e0 N)
      (b * sl) (uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
        (MS.primeStage.e0 N)) ≤
      (b : ℝ) * uniformUnitTupleProbability
        ((primorial (N + 1)) ^ MS.primeStage.e0 N) sl
        (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N)) := by
  classical
  let Q := (primorial (N + 1)) ^ MS.primeStage.e0 N
  let Eblock : Fin b → (Fin (b * sl) → Fin Q) → Prop := fun k p =>
    uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N)
      (fun j => p (pkgB2_replicaEmbedding k j))
  have hsubset (p : Fin (b * sl) → Fin Q) :
      uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
        (MS.primeStage.e0 N) p → ∃ k, Eblock k p := by
    intro h
    exact pkgB2_repUniformSmallException_subset hT (N + 1)
      (MS.primeStage.e0 N) p h
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact pow_pos (primorial_pos _) _
  calc
    _ ≤ uniformUnitTupleProbability Q (b * sl) (fun p => ∃ k, Eblock k p) :=
      pkgB2_uniformUnitTupleProbability_mono hsubset
    _ ≤ ∑ k : Fin b,
        uniformUnitTupleProbability Q (b * sl) (Eblock k) :=
      by
        simpa using
          (pkgB2_uniformUnitTupleProbability_exists_le Finset.univ Eblock)
    _ = ∑ _k : Fin b,
        uniformUnitTupleProbability Q sl
          (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact pkgB2_uniformUnitTupleProbability_iid_marginal hQpos
        (pkgB2_replicaEmbedding k)
        (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N))
    _ = (b : ℝ) * uniformUnitTupleProbability Q sl
        (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N)) := by
      simp [Q]

theorem pkgB2_repUniformSmallException_tendsto {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) :
    Tendsto
      (fun N : ℕ => uniformUnitTupleProbability
        ((primorial (N + 1)) ^ MS.primeStage.e0 N) (b * sl)
        (uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
          (MS.primeStage.e0 N))) atTop (𝓝 0) := by
  have hold := MS.primeStage.uniform_small_prime_exception
  have hlim : Tendsto
      (fun N : ℕ => (b : ℝ) * uniformUnitTupleProbability
        ((primorial (N + 1)) ^ MS.primeStage.e0 N) sl
        (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hold
  have hnonneg (N : ℕ) :
      0 ≤ uniformUnitTupleProbability
        ((primorial (N + 1)) ^ MS.primeStage.e0 N) (b * sl)
        (uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
          (MS.primeStage.e0 N)) :=
    pkgB2_uniformUnitTupleProbability_nonneg _
  have hupper : ∀ᶠ N : ℕ in atTop,
      uniformUnitTupleProbability
        ((primorial (N + 1)) ^ MS.primeStage.e0 N) (b * sl)
        (uniformSmallPrimeException (pkgB2_repTests hT) (N + 1)
          (MS.primeStage.e0 N)) ≤
        (b : ℝ) * uniformUnitTupleProbability
          ((primorial (N + 1)) ^ MS.primeStage.e0 N) sl
          (uniformSmallPrimeException Dm (N + 1) (MS.primeStage.e0 N)) :=
    Filter.Eventually.of_forall fun N =>
      pkgB2_repUniformSmallException_probability_bound MS T hT N
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hupper hlim

theorem pkgB2_poolMass_pos_eventually {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm) (l : Fin K) :
    ∀ᶠ N : ℕ in atTop,
      0 < primePoolMass (MS.primeStage.pool N l).lower
        (MS.primeStage.pool N l).upper := by
  have hratio := MS.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 ≤ primePoolMass (MS.primeStage.pool N l).lower
        (MS.primeStage.pool N l).upper /
          (masterScaleV MS.core.parameters N l : ℝ) := by
    simpa [pow_one] using hratio.eventually_ge_atTop (1 : ℝ)
  filter_upwards [hlarge] with N hN
  have hVpos : 0 < (masterScaleV MS.core.parameters N l : ℝ) := by
    unfold masterScaleV
    positivity
  have hmass := (le_div_iff₀ hVpos).mp hN
  have hmassPos :
      0 < primePoolMass (MS.primeStage.pool N l).lower
        (MS.primeStage.pool N l).upper := by
    linarith
  exact hmassPos

theorem pkgB2_repActualSmallException_probability_bound {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (l : Fin K)
    (hmass : 0 < primePoolMass (MS.primeStage.pool N l).lower
      (MS.primeStage.pool N l).upper) :
    independentPrimePoolProbability
      (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
      (fun _ => (MS.primeStage.pool N l).upper)
      (primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N)) ≤
    (b : ℝ) * independentPrimePoolProbability
      (fun _ : Fin sl => (MS.primeStage.pool N l).lower)
      (fun _ => (MS.primeStage.pool N l).upper)
      (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N)) := by
  classical
  let Eblock : Fin b → (Fin (b * sl) → ℕ) → Prop := fun k p =>
    primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N)
      (fun j => p (pkgB2_replicaEmbedding k j))
  have hsubset (p : Fin (b * sl) → ℕ) :
      primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N) p →
        ∃ k, Eblock k p := by
    intro h
    exact pkgB2_repActualSmallException_subset hT (N + 1)
      (MS.primeStage.e0 N) p h
  calc
    _ ≤ independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper) (fun p => ∃ k, Eblock k p) := by
      apply independentPrimePoolProbability_mono_of_support
      intro p hp hbad
      exact hsubset p hbad
    _ ≤ ∑ k : Fin b,
        independentPrimePoolProbability
          (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
          (fun _ => (MS.primeStage.pool N l).upper) (Eblock k) :=
      by
        simpa using pkgB2_independentPrimePoolProbability_exists_le
          (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
          (fun _ => (MS.primeStage.pool N l).upper) Finset.univ Eblock
    _ = ∑ _k : Fin b,
        independentPrimePoolProbability
          (fun _ : Fin sl => (MS.primeStage.pool N l).lower)
          (fun _ => (MS.primeStage.pool N l).upper)
          (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa [Eblock] using (independentPrimePoolProbability_iid_marginal
        (MS.primeStage.pool N l).lower (MS.primeStage.pool N l).upper hmass
        (pkgB2_replicaEmbedding k)
        (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N))).symm
    _ = (b : ℝ) * independentPrimePoolProbability
        (fun _ : Fin sl => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N)) := by
      simp

theorem pkgB2_repActualSmallException_tendsto {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (l : Fin K) :
    Tendsto
      (fun N : ℕ => independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N)))
      atTop (𝓝 0) := by
  have hold := MS.primeStage.actual_small_prime_exception l
  have hlim : Tendsto
      (fun N : ℕ => (b : ℝ) * independentPrimePoolProbability
        (fun _ : Fin sl => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hold
  have hnonneg (N : ℕ) : 0 ≤ independentPrimePoolProbability
      (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
      (fun _ => (MS.primeStage.pool N l).upper)
      (primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N)) :=
    independentPrimePoolProbability_nonneg _ _ _
  have hupper : ∀ᶠ N : ℕ in atTop,
      independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent (pkgB2_repTests hT) (N + 1) (MS.primeStage.e0 N)) ≤
      (b : ℝ) * independentPrimePoolProbability
        (fun _ : Fin sl => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (primeSmallDivisibilityEvent Dm (N + 1) (MS.primeStage.e0 N)) := by
    filter_upwards [pkgB2_poolMass_pos_eventually MS l] with N hmass
    exact pkgB2_repActualSmallException_probability_bound MS T hT N l hmass
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hupper hlim

theorem pkgB2_repZeroRepeat_superPolynomial {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (l : Fin K) :
    SuperPolynomialSmall
      (fun N => independentPrimePoolProbability
        (fun _ : Fin (b * sl) => (MS.primeStage.pool N l).lower)
        (fun _ => (MS.primeStage.pool N l).upper)
        (polynomialZeroOrRepeated (pkgB2_repTests hT)))
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)) := by
  classical
  let Drep := pkgB2_repTests hT
  let lo : ℕ → ℕ := fun N => (MS.primeStage.pool N l).lower
  let hi : ℕ → ℕ := fun N => (MS.primeStage.pool N l).upper
  let mass : ℕ → ℝ := fun N => primePoolMass (lo N) (hi N)
  let V : ℕ → ℝ := fun N => (masterScaleV MS.core.parameters N l : ℝ)
  let num : ℕ := (∑ P ∈ Drep, MvPolynomial.totalDegree P) + (b * sl) ^ 2
  have hDrep : ∀ P ∈ Drep, P ≠ 0 := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨k, hk, rfl⟩
    have hD : (T k).D ≠ 0 := (T k).tests_ne_zero (T k).D (T k).D_mem
    intro hzero
    apply hD
    exact MvPolynomial.rename_injective (pkgB2_templateEmbedding hT k)
      (pkgB2_templateEmbedding hT k).injective hzero
  have hLowerPos : ∀ᶠ N : ℕ in atTop, 0 < lo N := by
    have hratio := MS.primeStage.pool_lower_dominates l 1 (by norm_num)
    have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ (lo N : ℝ) / V N := by
      simpa [lo, V, pow_one] using hratio.eventually_ge_atTop (1 : ℝ)
    filter_upwards [hlarge] with N hN
    have hVpos : 0 < V N := by
      dsimp [V, masterScaleV]
      positivity
    have hVone : 1 ≤ V N := by
      have hVnat : 2 ≤ masterScaleV MS.core.parameters N l := by
        unfold masterScaleV
        omega
      simpa [V] using (show (1 : ℝ) ≤ (masterScaleV MS.core.parameters N l : ℝ) by
        exact_mod_cast le_trans (by norm_num : 1 ≤ 2) hVnat)
    have hVle : V N ≤ (lo N : ℝ) := by
      have h := (le_div_iff₀ hVpos).mp hN
      simpa [lo, pow_one] using h
    have hlo : 0 < (lo N : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans hVone hVle)
    exact_mod_cast hlo
  have hMassPos : ∀ᶠ N : ℕ in atTop, 0 < mass N := by
    simpa [mass, lo, hi] using pkgB2_poolMass_pos_eventually MS l
  have hnonneg (N : ℕ) : 0 ≤ independentPrimePoolProbability
      (fun _ : Fin (b * sl) => lo N) (fun _ => hi N)
      (polynomialZeroOrRepeated Drep) :=
    independentPrimePoolProbability_nonneg _ _ _
  intro C hC
  let Cplus : ℝ := C + 1
  have hCplus : 0 < Cplus := by dsimp [Cplus]; linarith
  have hMassDom : Tendsto (fun N => mass N / V N ^ Cplus) atTop atTop := by
    simpa [mass, V, lo, hi] using
      MS.primeStage.pool_harmonic_mass_dominates l Cplus hCplus
  have hInv : Tendsto (fun N => (mass N / V N ^ Cplus)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp hMassDom
  have hMassPositive : ∀ᶠ N : ℕ in atTop, 0 < mass N := hMassPos
  have hSmall : Tendsto (fun N => V N ^ Cplus / mass N) atTop (𝓝 0) := by
    have heq : (fun N => (mass N / V N ^ Cplus)⁻¹) =ᶠ[atTop]
        fun N => V N ^ Cplus / mass N := by
      filter_upwards [hMassPositive] with N hN
      have hV : 0 < V N := by
        dsimp [V, masterScaleV]
        positivity
      have hpow : 0 < V N ^ Cplus := Real.rpow_pos_of_pos hV Cplus
      field_simp
    exact hInv.congr' heq
  have hupper : ∀ᶠ N : ℕ in atTop,
      independentPrimePoolProbability (fun _ : Fin (b * sl) => lo N) (fun _ => hi N)
          (polynomialZeroOrRepeated Drep) * V N ^ C ≤
        (num : ℝ) * (V N ^ Cplus / mass N) := by
    filter_upwards [hLowerPos, hMassPos] with N hLo hMass
    have hlo : 0 < lo N := hLo
    have hbound := pool_zero_or_repeat_bound Drep hDrep (lo N) (hi N) hlo
    have hprob : independentPrimePoolProbability
        (fun _ : Fin (b * sl) => lo N) (fun _ => hi N)
        (polynomialZeroOrRepeated Drep) ≤
        (num : ℝ) / ((lo N : ℝ) * mass N) := by
      simpa [num, lo, hi, mass, Drep, Nat.cast_add, Nat.cast_mul] using hbound
    have hloOne : 1 ≤ (lo N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hlo.ne'
    have hden : mass N ≤ (lo N : ℝ) * mass N := by
      nlinarith [hMass]
    have hdiv : (num : ℝ) / ((lo N : ℝ) * mass N) ≤ (num : ℝ) / mass N :=
      div_le_div_of_nonneg_left (by positivity) hMass hden
    have hV : 1 ≤ V N := by
      have hVnat : 2 ≤ masterScaleV MS.core.parameters N l := by
        unfold masterScaleV
        omega
      simpa [V] using (show (1 : ℝ) ≤ (masterScaleV MS.core.parameters N l : ℝ) by
        exact_mod_cast le_trans (by norm_num : 1 ≤ 2) hVnat)
    have hVpos : 0 < V N := lt_of_lt_of_le (by norm_num) hV
    have hpowEq : V N ^ Cplus = V N ^ C * V N := by
      dsimp [Cplus]
      rw [Real.rpow_add hVpos, Real.rpow_one]
    have hpow : V N ^ C ≤ V N ^ Cplus := by
      rw [hpowEq]
      simpa using mul_le_mul_of_nonneg_left hV (Real.rpow_nonneg hVpos.le C)
    have hdivDen : V N ^ C / ((lo N : ℝ) * mass N) ≤ V N ^ C / mass N :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hVpos.le C) hMass hden
    have hdivPow : V N ^ C / mass N ≤ V N ^ Cplus / mass N :=
      div_le_div_of_nonneg_right hpow hMass.le
    calc
      _ ≤ ((num : ℝ) / ((lo N : ℝ) * mass N)) * V N ^ C :=
        mul_le_mul_of_nonneg_right hprob (Real.rpow_nonneg (by positivity) C)
      _ = (num : ℝ) * (V N ^ C / ((lo N : ℝ) * mass N)) := by ring
      _ ≤ (num : ℝ) * (V N ^ C / mass N) :=
        mul_le_mul_of_nonneg_left hdivDen (by positivity)
      _ ≤ (num : ℝ) * (V N ^ Cplus / mass N) :=
        mul_le_mul_of_nonneg_left hdivPow (by positivity)
  have hlim : Tendsto (fun N => (num : ℝ) * (V N ^ Cplus / mass N)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hSmall)
  exact squeeze_zero' (Filter.Eventually.of_forall fun N =>
      mul_nonneg (hnonneg N) (Real.rpow_nonneg (by positivity) C)) hupper hlim

theorem pkgB2_repGapModulus_divides {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (l : Fin K) (p : Fin (b * sl) → ℕ)
    (hpool : ∀ i, (MS.primeStage.pool N l).lower ≤ p i ∧
      p i < (MS.primeStage.pool N l).upper ∧ (p i).Prime)
    (Q : IntegerPolynomial (b * sl)) (hQ : Q ∈ pkgB2_repTests hT)
    (hQne : evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0) :
    MS.core.parameters.M N *
      (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∣
        MS.core.parameters.H N l := by
  classical
  rcases Finset.mem_image.mp hQ with ⟨k, hk, rfl⟩
  let ι : Fin (T k).q ↪ Fin sl := Classical.choose (hT k)
  let pblock : Fin sl → ℕ := fun j => p (pkgB2_replicaEmbedding k j)
  have hlisted : MvPolynomial.rename ι (T k).D ∈ Dm :=
    (Classical.choose_spec (hT k)) (T k).D (T k).D_mem
  have hblock : ∀ j, (MS.primeStage.pool N l).lower ≤ pblock j ∧
      pblock j < (MS.primeStage.pool N l).upper ∧ (pblock j).Prime := by
    intro j
    exact hpool (pkgB2_replicaEmbedding k j)
  have hEval :
      evalIntegerPolynomial
          (MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D)
          (fun i => (p i : ℤ)) =
        evalIntegerPolynomial (MvPolynomial.rename ι (T k).D)
          (fun j => (pblock j : ℤ)) := by
    rw [pkgB2_renameEval (pkgB2_templateEmbedding hT k) (T k).D p]
    rw [pkgB2_renameEval ι (T k).D pblock]
    rfl
  have hmaster := MS.gapStage.polynomial_values_divide_gap N l pblock
    (MvPolynomial.rename ι (T k).D) hlisted hblock (by simpa [hEval] using hQne)
  simpa [hEval] using hmaster

noncomputable def pkgB2_repScales {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) :
    MasterScales K As (b * sl) (pkgB2_repTests hT) :=
  pkgB2_repScalesOfFacts MS T hT
    (pkgB2_repUniformSmallException_tendsto MS T hT)
    (fun l => pkgB2_repActualSmallException_tendsto MS T hT l)
    (fun l => pkgB2_repZeroRepeat_superPolynomial MS T hT l)
    (fun N l p Q hQ hp hne =>
      pkgB2_repGapModulus_divides MS T hT N l p hp Q hQ hne)

abbrev pkgB2_Coord {b : ℕ} (T : Fin b → CubeTemplate) :=
  pkgB2_OldCoord T ⊕ (pkgB2_Nonroot T × Fin 2)

def pkgB2_activeRow {b : ℕ} (T : Fin b → CubeTemplate)
    (t : pkgB2_BaseRow T) (r : pkgB2_Nonroot T) : Prop :=
  t ≠ Sum.inr r

abbrev pkgB2_Occurrence {b : ℕ} (T : Fin b → CubeTemplate)
    (E : Finset (pkgB2_Nonroot T)) :=
  pkgB2_Copy (pkgB2_activeRow T) E

noncomputable instance pkgB2_nonrootFintype {b : ℕ} (T : Fin b → CubeTemplate) :
    Fintype (pkgB2_Nonroot T) := Fintype.ofFinite _

noncomputable instance pkgB2_rowFintype {b : ℕ} (T : Fin b → CubeTemplate) :
    Fintype (pkgB2_BaseRow T) := Fintype.ofFinite _

noncomputable instance pkgB2_coordFintype {b : ℕ} (T : Fin b → CubeTemplate) :
    Fintype (pkgB2_Coord T) := Fintype.ofFinite _

noncomputable instance pkgB2_occurrenceFintype {b : ℕ} (T : Fin b → CubeTemplate)
    (E : Finset (pkgB2_Nonroot T)) : Fintype (pkgB2_Occurrence T E) := Fintype.ofFinite _

private noncomputable def pkgB2_directionConstantBound {b : ℕ}
    (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) : ℕ := by
  classical
  exact ∑ r : pkgB2_Nonroot T,
    ((direction r 0).natAbs +
      ∑ ω : Finset (Fin (T r.1).d),
        (direction r 0 + ∑ j ∈ ω, direction r j.succ).natAbs)

private theorem pkgB2_directionConstantBound_root {b : ℕ}
    (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (r : pkgB2_Nonroot T) :
    (direction r 0).natAbs ≤ pkgB2_directionConstantBound T direction := by
  classical
  unfold pkgB2_directionConstantBound
  calc
    (direction r 0).natAbs ≤
        (direction r 0).natAbs +
          ∑ ω : Finset (Fin (T r.1).d),
            (direction r 0 + ∑ j ∈ ω, direction r j.succ).natAbs := Nat.le_add_right _ _
    _ ≤ ∑ s : pkgB2_Nonroot T,
          ((direction s 0).natAbs +
            ∑ ω : Finset (Fin (T s.1).d),
              (direction s 0 + ∑ j ∈ ω, direction s j.succ).natAbs) :=
      Finset.single_le_sum
        (f := fun s : pkgB2_Nonroot T => (direction s 0).natAbs +
          ∑ ω : Finset (Fin (T s.1).d),
            (direction s 0 + ∑ j ∈ ω, direction s j.succ).natAbs)
        (fun s _ => Nat.zero_le _)
        (Finset.mem_univ r)

private theorem pkgB2_directionConstantBound_other {b : ℕ}
    (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (r : pkgB2_Nonroot T) (ω : Finset (Fin (T r.1).d)) :
    (direction r 0 + ∑ j ∈ ω, direction r j.succ).natAbs ≤
      pkgB2_directionConstantBound T direction := by
  classical
  unfold pkgB2_directionConstantBound
  have hinner :
      (direction r 0 + ∑ j ∈ ω, direction r j.succ).natAbs ≤
        ∑ ω' : Finset (Fin (T r.1).d),
          (direction r 0 + ∑ j ∈ ω', direction r j.succ).natAbs :=
    Finset.single_le_sum
      (f := fun ω' : Finset (Fin (T r.1).d) =>
        (direction r 0 + ∑ j ∈ ω', direction r j.succ).natAbs)
      (fun ω' _ => Nat.zero_le _)
      (Finset.mem_univ ω)
  have hterm :
      ∑ ω' : Finset (Fin (T r.1).d),
          (direction r 0 + ∑ j ∈ ω', direction r j.succ).natAbs ≤
        (direction r 0).natAbs +
          ∑ ω' : Finset (Fin (T r.1).d),
            (direction r 0 + ∑ j ∈ ω', direction r j.succ).natAbs :=
    Nat.le_add_left _ _
  exact hinner.trans (hterm.trans <| Finset.single_le_sum
    (f := fun s : pkgB2_Nonroot T => (direction s 0).natAbs +
      ∑ ω' : Finset (Fin (T s.1).d),
        (direction s 0 + ∑ j ∈ ω', direction s j.succ).natAbs)
    (fun s _ => Nat.zero_le _)
    (Finset.mem_univ r))

private theorem pkgB2_intCast_ne_zero_of_natAbs_lt {r : ℕ} (c : ℤ)
    (hc : c ≠ 0) (hbound : c.natAbs < r) : (c : ZMod r) ≠ 0 := by
  intro hz
  have hdivZ : (r : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c r).mp hz
  have hdivN : r ∣ c.natAbs := Int.natCast_dvd.mp hdivZ
  have habspos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hle : r ≤ c.natAbs := Nat.le_of_dvd habspos hdivN
  omega

private theorem pkgB2_directionSpec_modulo {b : ℕ} (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction)
    (N r : ℕ) (hN : pkgB2_directionConstantBound T direction + 1 ≤ N)
    (hrN : N + 1 < r) (s : pkgB2_Nonroot T) :
    (direction s 0 : ZMod r) ≠ 0 ∧
      ∀ ω' : Finset (Fin (T s.1).d), ω' ≠ s.2.1 →
        (direction s 0 : ZMod r) +
          ∑ j ∈ ω', (direction s j.succ : ZMod r) ≠ 0 := by
  have hrBound : pkgB2_directionConstantBound T direction < r := by omega
  constructor
  · apply pkgB2_intCast_ne_zero_of_natAbs_lt
    · exact (hdir s).1
    · exact lt_of_le_of_lt
        (pkgB2_directionConstantBound_root T direction s) hrBound
  · intro ω' hω
    let c : ℤ := direction s 0 + ∑ j ∈ ω', direction s j.succ
    have hcInt : c ≠ 0 := (hdir s).2.2 ω' hω
    have hbound : c.natAbs < r := by
      exact lt_of_le_of_lt (pkgB2_directionConstantBound_other T direction s ω') hrBound
    have hc : (c : ZMod r) ≠ 0 := pkgB2_intCast_ne_zero_of_natAbs_lt c hcInt hbound
    have hcast : (c : ZMod r) =
        (direction s 0 : ZMod r) + ∑ j ∈ ω', (direction s j.succ : ZMod r) := by
      dsimp [c]
      simp
    rw [hcast] at hc
    exact hc

noncomputable def pkgB2_occurrenceEnum {b : ℕ} (T : Fin b → CubeTemplate)
    (E : Finset (pkgB2_Nonroot T)) : Fin (Fintype.card (pkgB2_Occurrence T E)) ≃
      pkgB2_Occurrence T E := (Fintype.equivFin _).symm

noncomputable def pkgB2_coordEnum {b : ℕ} (T : Fin b → CubeTemplate) :
    Fin (Fintype.card (pkgB2_Coord T)) ≃ pkgB2_Coord T :=
  (Fintype.equivFin _).symm

/-- Coefficients of the unreplicated cube rows on the pivot and original shift coordinates. -/
noncomputable def pkgB2_oldCoefficient {b : ℕ} (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (t : pkgB2_BaseRow T) (c : pkgB2_OldCoord T) : ℤ :=
  match t with
  | .inl _ => match c with
      | .inl _ => 1
      | .inr _ => 0
  | .inr r => match c with
      | .inl _ => 1
      | .inr ⟨k, (j, side)⟩ =>
          if hk : k = r.1 then
            if (hk ▸ j) ∈ r.2.1 then
              if side.val = 0 then -M r.1 else M r.1 else 0
          else 0

noncomputable def pkgB2_occurrenceCoefficientInt {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (o : pkgB2_Occurrence T E) :
    pkgB2_Coord T → ℤ :=
  pkgB2_copyCoeffInt
    (fun t c => pkgB2_oldCoefficient T (fun k => (M k : ℤ)) t c)
    (fun t r => pkgB2_response T (fun k => (M k : ℤ)) r
      (pkgB2_directionLift (T r.1).d (direction r)) t)
    (pkgB2_activeRow T) E o

noncomputable def pkgB2_occurrenceCoefficient {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (o : pkgB2_Occurrence T E) :
    pkgB2_Coord T → ℚ :=
  fun c => (pkgB2_occurrenceCoefficientInt T M direction E o c : ℚ)

private theorem pkgB2_occurrenceCoefficient_eq_castInt {b : ℕ}
    (T : Fin b → CubeTemplate) (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (o : pkgB2_Occurrence T E)
    (c : pkgB2_Coord T) :
    pkgB2_occurrenceCoefficient T M direction E o c =
      (pkgB2_occurrenceCoefficientInt T M direction E o c : ℚ) := by
  rfl

private theorem pkgB2_rationalResidue_intCast (r : ℕ) (hr : r.Prime) (z : ℤ) :
    rationalResidue r hr (z : ℚ) = (z : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  simp [rationalResidue]

private theorem pkgB2_oldCoefficient_anchor {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℤ) (t : pkgB2_BaseRow T) :
    pkgB2_oldCoefficient T M t (.inl ()) = 1 := by
  cases t <;> rfl

private noncomputable def pkgB2_oldCoefficientField {b : ℕ} {F : Type*} [Field F]
    (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (t : pkgB2_BaseRow T) (c : pkgB2_OldCoord T) : F :=
  (pkgB2_oldCoefficient T M t c : F)

private theorem pkgB2_finset_membership_diff {α : Type*} [DecidableEq α]
    (s t : Finset α) (hst : s ≠ t) :
    ∃ a, (a ∈ s ∧ a ∉ t) ∨ (a ∉ s ∧ a ∈ t) := by
  classical
  by_contra h
  have hsame (a : α) : a ∈ s ↔ a ∈ t := by
    constructor
    · intro hs
      by_contra ht
      exact h ⟨a, Or.inl ⟨hs, ht⟩⟩
    · intro ht
      by_contra hs
      exact h ⟨a, Or.inr ⟨hs, ht⟩⟩
  apply hst
  ext a
  exact hsame a

private theorem pkgB2_oldRows_separate {b : ℕ} {F : Type*} [Field F]
    (T : Fin b → CubeTemplate) (M : Fin b → ℤ)
    (hM : ∀ k, (M k : F) ≠ 0)
    (t s : pkgB2_BaseRow T) (hts : t ≠ s) :
    ∃ c : pkgB2_OldCoord T,
      pkgB2_oldCoefficientField (F := F) T M t c ≠
        pkgB2_oldCoefficientField (F := F) T M s c := by
  classical
  cases t with
  | inl _ =>
      cases s with
      | inl _ => exact False.elim (hts rfl)
      | inr r =>
          rcases r with ⟨k, ω⟩
          obtain ⟨j, hj⟩ := ω.2
          refine ⟨.inr ⟨k, (j, 0)⟩, ?_⟩
          have hroot : pkgB2_oldCoefficientField (F := F) T M (.inl ())
              (.inr ⟨k, (j, 0)⟩) = 0 := by
            simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient]
          have hrow : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω⟩)
              (.inr ⟨k, (j, 0)⟩) = -(M k : F) := by
            simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj]
          rw [hroot, hrow]
          exact (neg_ne_zero.mpr (hM k)).symm
  | inr r =>
      rcases r with ⟨k, ω⟩
      cases s with
      | inl _ =>
          obtain ⟨j, hj⟩ := ω.2
          refine ⟨.inr ⟨k, (j, 0)⟩, ?_⟩
          have hrow : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω⟩)
              (.inr ⟨k, (j, 0)⟩) = -(M k : F) := by
            simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj]
          have hroot : pkgB2_oldCoefficientField (F := F) T M (.inl ())
              (.inr ⟨k, (j, 0)⟩) = 0 := by
            simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient]
          rw [hrow, hroot]
          exact neg_ne_zero.mpr (hM k)
      | inr s =>
          rcases s with ⟨k', ω'⟩
          by_cases hkk : k = k'
          · subst k'
            have hω : ω.1 ≠ ω'.1 := by
              intro hEq
              apply hts
              have hsub : ω = ω' := Subtype.ext hEq
              subst ω'
              rfl
            obtain ⟨j, hj | hj⟩ := pkgB2_finset_membership_diff ω.1 ω'.1 hω
            · refine ⟨.inr ⟨k, (j, 0)⟩, ?_⟩
              have htval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω⟩)
                  (.inr ⟨k, (j, 0)⟩) = -(M k : F) := by
                simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj.1]
              have hsval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω'⟩)
                  (.inr ⟨k, (j, 0)⟩) = 0 := by
                simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj.2]
              rw [htval, hsval]
              exact neg_ne_zero.mpr (hM k)
            · refine ⟨.inr ⟨k, (j, 0)⟩, ?_⟩
              have htval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω⟩)
                  (.inr ⟨k, (j, 0)⟩) = 0 := by
                simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj.1]
              have hsval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω'⟩)
                  (.inr ⟨k, (j, 0)⟩) = -(M k : F) := by
                simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj.2]
              rw [htval, hsval]
              exact (neg_ne_zero.mpr (hM k)).symm
          · obtain ⟨j, hj⟩ := ω.2
            refine ⟨.inr ⟨k, (j, 0)⟩, ?_⟩
            have htval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k, ω⟩)
                (.inr ⟨k, (j, 0)⟩) = -(M k : F) := by
              simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hj]
            have hsval : pkgB2_oldCoefficientField (F := F) T M (.inr ⟨k', ω'⟩)
                (.inr ⟨k, (j, 0)⟩) = 0 := by
              simp [pkgB2_oldCoefficientField, pkgB2_oldCoefficient, hkk]
            rw [htval, hsval]
            exact neg_ne_zero.mpr (hM k)

private theorem pkgB2_occurrenceCoefficient_anchor {b : ℕ} (T : Fin b → CubeTemplate)
    (M : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (o : pkgB2_Occurrence T E) :
    pkgB2_occurrenceCoefficient T M direction E o (.inl (.inl ())) = 1 := by
  cases hrow : o.1 <;>
    simp [pkgB2_occurrenceCoefficient, pkgB2_occurrenceCoefficientInt,
      pkgB2_copyCoeffInt, pkgB2_oldCoefficient, hrow]

noncomputable def pkgB2_rowCoefficientArray {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) :
    ℕ → (Fin (b * sl) → ℕ) →
      Fin (Fintype.card (pkgB2_Occurrence T E)) →
        Fin (Fintype.card (pkgB2_Coord T)) → ℚ := by
  classical
  exact fun N p u j =>
    pkgB2_occurrenceCoefficient T
      (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
      direction E ((pkgB2_occurrenceEnum T E) u)
        ((pkgB2_coordEnum T) j)

private theorem pkgB2_rowCoefficientArray_ownDirection_zero {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (r : pkgB2_Nonroot T) (hrow : (pkgB2_occurrenceEnum T E u).1 = Sum.inr r) :
    pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u
      ((pkgB2_coordEnum T).symm (.inr (r, (0 : Fin 2)))) = 0 := by
  classical
  let Mnat : Fin b → ℕ := fun k =>
    (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
  let Mint : Fin b → ℤ := fun k => (Mnat k : ℤ)
  have hresponse : pkgB2_response T Mint r
      (pkgB2_directionLift (T r.1).d (direction r)) (.inr r) = 0 := by
    apply pkgB2_response_self
    simpa [pkgB2_directionLift_zero, pkgB2_directionLift_sum] using (hdir r).2.1
  have hcoeffInt : pkgB2_occurrenceCoefficientInt T Mnat direction E
      (pkgB2_occurrenceEnum T E u) (.inr (r, (0 : Fin 2))) = 0 := by
    simp [pkgB2_occurrenceCoefficientInt, pkgB2_copyCoeffInt,
      pkgB2_activeRow, hrow, hresponse, Mint]
  have hcoeff : pkgB2_occurrenceCoefficient T Mnat direction E
      (pkgB2_occurrenceEnum T E u) (.inr (r, (0 : Fin 2))) = 0 := by
    simp [pkgB2_occurrenceCoefficient, hcoeffInt]
  unfold pkgB2_rowCoefficientArray
  rw [Equiv.apply_symm_apply]
  simpa [Mnat] using hcoeff

private theorem pkgB2_rowCoefficientArray_anchor {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (p : Fin (b * sl) → ℕ) (u : Fin (Fintype.card (pkgB2_Occurrence T E))) :
    pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u
      ((pkgB2_coordEnum T).symm (.inl (.inl ()))) = 1 := by
  classical
  unfold pkgB2_rowCoefficientArray
  rw [Equiv.apply_symm_apply]
  exact pkgB2_occurrenceCoefficient_anchor T
    (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
    direction E ((pkgB2_occurrenceEnum T E) u)

private theorem pkgB2_rowCoefficientArray_root_residue {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (r : ℕ) (hr : r.Prime) :
    rationalResidue r hr
      (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u
        ((pkgB2_coordEnum T).symm (.inl (.inl ()))) ) = 1 := by
  rw [pkgB2_rowCoefficientArray_anchor]
  letI : Fact r.Prime := ⟨hr⟩
  simp [rationalResidue]

private theorem pkgB2_rowCoefficientArray_eq_castInt {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (j : Fin (Fintype.card (pkgB2_Coord T))) :
    pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j =
      (pkgB2_occurrenceCoefficientInt T
        (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
        direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j) : ℚ) := by
  unfold pkgB2_rowCoefficientArray
  exact pkgB2_occurrenceCoefficient_eq_castInt T
    (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
    direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j)

private theorem pkgB2_rowCoefficientArray_residue_eq_intCast {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (j : Fin (Fintype.card (pkgB2_Coord T))) (r : ℕ) (hr : r.Prime) :
    rationalResidue r hr
        (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j) =
      ((pkgB2_occurrenceCoefficientInt T
        (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
        direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j) : ℤ) : ZMod r) := by
  unfold pkgB2_rowCoefficientArray pkgB2_occurrenceCoefficient
  exact pkgB2_rationalResidue_intCast r hr
    (pkgB2_occurrenceCoefficientInt T
      (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
      direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j))

private theorem pkgB2_rowCoefficientArray_den_eq_one {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (j : Fin (Fintype.card (pkgB2_Coord T))) :
    (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j).den = 1 := by
  rw [pkgB2_rowCoefficientArray_eq_castInt]
  simp

private theorem pkgB2_rowCoefficientArray_residue_eq_copyCoeff {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (j : Fin (Fintype.card (pkgB2_Coord T)))
    (r : ℕ) (hr : r.Prime) [Fact r.Prime] :
    rationalResidue r hr
        (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j) =
      pkgB2_copyCoeff
        (fun t c =>
          ((pkgB2_oldCoefficient T
            (fun k => ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℤ))
            t c : ℤ) : ZMod r))
        (fun t s =>
          ((pkgB2_response T
            (fun k => ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℤ))
            s (pkgB2_directionLift (T s.1).d (direction s)) t : ℤ) : ZMod r))
        (pkgB2_activeRow T) E ((pkgB2_occurrenceEnum T E) u)
        ((pkgB2_coordEnum T) j) := by
  classical
  let Mnat : Fin b → ℕ := fun k =>
    (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
  let Mint : Fin b → ℤ := fun k => (Mnat k : ℤ)
  let cInt : pkgB2_BaseRow T → pkgB2_OldCoord T → ℤ :=
    fun t c => pkgB2_oldCoefficient T Mint t c
  let rhoInt : pkgB2_BaseRow T → pkgB2_Nonroot T → ℤ :=
    fun t s => pkgB2_response T Mint s
      (pkgB2_directionLift (T s.1).d (direction s)) t
  let o := (pkgB2_occurrenceEnum T E) u
  let coord := (pkgB2_coordEnum T) j
  have hrow := pkgB2_rowCoefficientArray_residue_eq_intCast
    MS T hT J0 gap direction E N p u j r hr
  have hocc : pkgB2_occurrenceCoefficientInt T Mnat direction E o coord =
      pkgB2_copyCoeffInt cInt rhoInt (pkgB2_activeRow T) E o coord := rfl
  have hoccCast :
      ((pkgB2_occurrenceCoefficientInt T Mnat direction E o coord : ℤ) : ZMod r) =
        (pkgB2_copyCoeffInt cInt rhoInt (pkgB2_activeRow T) E o coord : ZMod r) :=
    congrArg (fun z : ℤ => (z : ZMod r)) hocc
  have hcopy :
      pkgB2_copyCoeff (fun t c => (cInt t c : ZMod r))
          (fun t s => (rhoInt t s : ZMod r)) (pkgB2_activeRow T) E o coord =
        (pkgB2_copyCoeffInt cInt rhoInt (pkgB2_activeRow T) E o coord : ZMod r) :=
    pkgB2_copyCoeff_eq_castInt (F := ZMod r) cInt rhoInt
      (pkgB2_activeRow T) E o coord
  rw [hrow, hoccCast]
  change (pkgB2_copyCoeffInt cInt rhoInt (pkgB2_activeRow T) E o coord : ZMod r) =
    pkgB2_copyCoeff (fun t c => (cInt t c : ZMod r))
      (fun t s => (rhoInt t s : ZMod r)) (pkgB2_activeRow T) E o coord
  exact hcopy.symm

private theorem pkgB2_linearRowValue_eq_castInt {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    linearRowValue (pkgB2_rowCoefficientArray MS T hT J0 gap direction E)
        N p u x =
      ((∑ j : Fin (Fintype.card (pkgB2_Coord T)),
        pkgB2_occurrenceCoefficientInt T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
          direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j) * x j : ℤ) : ℚ) := by
  classical
  unfold linearRowValue
  calc
    (∑ j, pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j * (x j : ℚ)) =
        ∑ j, ((pkgB2_occurrenceCoefficientInt T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
          direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j) * x j : ℤ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [pkgB2_rowCoefficientArray_eq_castInt]
          simp only [Int.cast_mul]
    _ = ((∑ j : Fin (Fintype.card (pkgB2_Coord T)),
        pkgB2_occurrenceCoefficientInt T
          (fun k => (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k))
          direction E ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j) * x j : ℤ) : ℚ) := by
          rw [Int.cast_sum]

private theorem pkgB2_linearRowValue_den_eq_one {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    (linearRowValue (pkgB2_rowCoefficientArray MS T hT J0 gap direction E)
      N p u x).den = 1 := by
  rw [pkgB2_linearRowValue_eq_castInt]
  simp only [Rat.den_intCast]

private theorem pkgB2_roughPart_le_natAbs {w : ℕ} {a : ℤ} (ha : a ≠ 0) :
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

private theorem pkgB2_roughPart_pos (w : ℕ) (a : ℤ) : 0 < roughPart w a := by
  classical
  unfold roughPart
  apply lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
  apply Finset.one_le_prod
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2.1
  exact one_le_pow₀ (le_trans (by norm_num) hpPrime.two_le)

private theorem pkgB2_prime_dvd_roughPart_implies_dvd_natAbs {w r : ℕ} {a : ℤ}
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

private theorem pkgB2_momentPolynomialEval_natAbs_le {q : ℕ}
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

private def pkgB2_momentPolynomialCoefficientMass {q : ℕ} (P : IntegerPolynomial q) : ℕ :=
  ∑ d ∈ P.support, (P.coeff d).natAbs

private noncomputable def pkgB2_momentShiftLengthLower {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate) (J0 N : ℕ) : ℕ :=
  MS.core.parameters.H N l /
    (J0 * (MS.core.parameters.M N *
      ((pkgB2_momentPolynomialCoefficientMass T.D + 1) *
        ((MS.primeStage.pool N l).upper + 1) ^ T.D.totalDegree)))

private def pkgB2_momentGapScale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (N : ℕ) : ℕ :=
  (MS.primeStage.pool N l).upper + masterScaleV MS.core.parameters N l

private theorem pkgB2_momentMasterScaleV_tendsto {K : ℕ} (A : Parameters K) (l : Fin K) :
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

private theorem pkgB2_momentGapScale_tendsto {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) :
    Tendsto (pkgB2_momentGapScale MS l) atTop atTop := by
  have hV := pkgB2_momentMasterScaleV_tendsto MS.core.parameters l
  rw [tendsto_atTop]
  intro n
  filter_upwards [hV.eventually_ge_atTop n] with N hN
  dsimp [pkgB2_momentGapScale]
  omega


private theorem pkgB2_momentShiftLength_lower {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate)
    (J0 N : ℕ) (hJ0 : 0 < J0) (p : Fin T.q → ℕ)
    (hgood : T.Good (corrScales MS) l N p) :
    pkgB2_momentShiftLengthLower MS l T J0 N ≤ T.length (corrScales MS) l J0 N p := by
  classical
  let U := (MS.primeStage.pool N l).upper
  let A := MS.core.parameters
  let value := evalIntegerPolynomial T.D (fun i => (p i : ℤ))
  let C := pkgB2_momentPolynomialCoefficientMass T.D
  rcases hgood with ⟨hp, hinj, htests, hsmall⟩
  have hpBound : ∀ i, p i ≤ U := fun i => (hp i).2.1.le
  have hEval := pkgB2_momentPolynomialEval_natAbs_le T.D U p hpBound
  have hrough := pkgB2_roughPart_le_natAbs (w := N + 1) (a := value) (htests T.D T.D_mem)
  have hmodle : A.M N * roughPart (N + 1) value ≤
      A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree) := by
    calc
      A.M N * roughPart (N + 1) value ≤
          A.M N * (C * (U + 1) ^ T.D.totalDegree) :=
        Nat.mul_le_mul_left _ (hrough.trans (by simpa [value, C, pkgB2_momentPolynomialCoefficientMass] using hEval))
      _ ≤ A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree) :=
        Nat.mul_le_mul_left (A.M N)
          (Nat.mul_le_mul_right ((U + 1) ^ T.D.totalDegree) (Nat.le_add_right C 1))
  let denUpper := J0 * (A.M N * ((C + 1) * (U + 1) ^ T.D.totalDegree))
  have hdenle : J0 * (A.M N * roughPart (N + 1) value) ≤
      denUpper := by
    dsimp [denUpper]
    exact Nat.mul_le_mul_left J0 hmodle
  have hdenpos : 0 < J0 * (A.M N * roughPart (N + 1) value) :=
    Nat.mul_pos hJ0 (Nat.mul_pos (A.Mpos N) (pkgB2_roughPart_pos (N + 1) value))
  unfold pkgB2_momentShiftLengthLower
  unfold CubeTemplate.length shiftLength directionModulus
  dsimp [U, A, C, pkgB2_momentPolynomialCoefficientMass] at hdenle ⊢
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

private theorem pkgB2_momentShiftLengthLower_ge_pow {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate)
    (J0 : ℕ) (hJ0 : 0 < J0) (m : ℕ) :
    ∀ᶠ N in atTop, (pkgB2_momentGapScale MS l N) ^ m ≤ pkgB2_momentShiftLengthLower MS l T J0 N := by
  classical
  let Cplus := pkgB2_momentPolynomialCoefficientMass T.D + 1
  let degree := T.D.totalDegree
  let E := 3 + degree
  let e : ℝ := (m + E + 1 : ℕ)
  have he : 0 < e := by dsimp [e, E]; positivity
  have hGap := MS.gapStage.gap_dominates_pool_and_bound l e he
  have hRatio : Tendsto
      (fun N => (MS.core.parameters.H N l : ℝ) /
        (pkgB2_momentGapScale MS l N : ℝ) ^ e) atTop atTop := by
    apply hGap.congr'
    filter_upwards with N
    simp [pkgB2_momentGapScale]
  have hScale := pkgB2_momentGapScale_tendsto MS l
  have hJ : ∀ᶠ N : ℕ in atTop, J0 ≤ pkgB2_momentGapScale MS l N :=
    hScale.eventually_ge_atTop J0
  have hC : ∀ᶠ N : ℕ in atTop, Cplus ≤ pkgB2_momentGapScale MS l N :=
    hScale.eventually_ge_atTop Cplus
  have hRatioOne : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ (MS.core.parameters.H N l : ℝ) /
        (pkgB2_momentGapScale MS l N : ℝ) ^ e :=
    hRatio.eventually_ge_atTop 1
  filter_upwards [hJ, hC, hRatioOne] with N hJN hCN hRN
  let S := pkgB2_momentGapScale MS l N
  let U := (MS.primeStage.pool N l).upper
  let Dupper := J0 * (MS.core.parameters.M N * (Cplus * (U + 1) ^ degree))
  have hSpos : 0 < S := by dsimp [S, pkgB2_momentGapScale, masterScaleV]; omega
  have hSone : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr hSpos.ne'
  have hMle : MS.core.parameters.M N ≤ S := by
    dsimp [S, pkgB2_momentGapScale, masterScaleV]
    omega
  have hUle : U + 1 ≤ S := by
    dsimp [S, pkgB2_momentGapScale, masterScaleV, U]
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
  simpa [pkgB2_momentShiftLengthLower, Cplus, degree, Dupper, U, S, pkgB2_momentGapScale] using hq

theorem pkgB2_blockScale_le_momentGapScale {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (hgap : ∀ k, ValidGap B (gap k)) (k : Fin b) (N : ℕ) :
    pkgB2_blockScale MS.core.parameters B N ≤ pkgB2_momentGapScale MS (gap k) N := by
  have h := pkgB2_blockScale_le_masterScaleV MS.core.parameters B (gap k)
    (hgap k).1 N
  dsimp [pkgB2_momentGapScale]
  omega

theorem pkgB2_shiftLengthFloor_le_actual {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (hJ0 : ∀ k, 0 < J0 k) (N : ℕ) (p : (k : Fin b) → Fin (T k).q → ℕ)
    (hgood : ∀ k, (T k).Good (corrScales MS) (gap k) N (p k)) (k : Fin b) :
    pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N ≤
      (T k).length (corrScales MS) (gap k) (J0 k) N (p k) := by
  exact pkgB2_momentShiftLength_lower MS (gap k) (T k) (J0 k) N
    (hJ0 k) (p k) (hgood k)

theorem pkgB2_shiftLengthFloor_ge_blockScale_pow {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (k : Fin b) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (pkgB2_blockScale MS.core.parameters B N) ^ m ≤
        pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
  have hfloor := pkgB2_momentShiftLengthLower_ge_pow MS (gap k) (T k)
    (J0 k) (hJ0 k) m
  have hscale : ∀ N,
      pkgB2_blockScale MS.core.parameters B N ≤ pkgB2_momentGapScale MS (gap k) N :=
    fun N => pkgB2_blockScale_le_momentGapScale MS B gap T hgap k N
  filter_upwards [hfloor] with N hN
  exact (Nat.pow_le_pow_left (hscale N) m).trans hN

theorem pkgB2_translationLength_ge_blockScale_pow {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (k : Fin b) (c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (pkgB2_blockScale MS.core.parameters B N) ^ c ≤
        Nat.sqrt (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) := by
  have hfloor := pkgB2_shiftLengthFloor_ge_blockScale_pow MS B T J0 gap hgap hJ0 k (2 * c)
  filter_upwards [hfloor] with N hN
  apply (Nat.le_sqrt').2
  have hpow :
      ((pkgB2_blockScale MS.core.parameters B N) ^ c) ^ 2 =
        (pkgB2_blockScale MS.core.parameters B N) ^ (2 * c) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow]
  exact hN

noncomputable def pkgB2_shiftLength {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (hT : ∀ k, Allowed Dm (T k)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (k : Fin b) : ℕ :=
  (T k).length (corrScales MS) (gap k) (J0 k) N (pkgB2_repPrimeProject hT p k)

noncomputable def pkgB2_translationLength {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (k : Fin b) (N : ℕ) : ℕ :=
  Nat.sqrt (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N)

noncomputable def pkgB2_baseRegular {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) : Prop :=
  (∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)) ∧
  (∀ k, 0 < pkgB2_shiftLength MS T J0 gap hT N p k) ∧
  (∀ k, 0 < pkgB2_translationLength MS T J0 gap k N)

private theorem pkgB2_baseRegular_of_allGood_eventually {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      (∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)) →
        pkgB2_baseRegular MS B T J0 gap hT N p := by
  have hshift (k : Fin b) :
      ∀ᶠ N : ℕ in atTop,
        (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
          pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N :=
    pkgB2_shiftLengthFloor_ge_blockScale_pow MS B T J0 gap hgap hJ0 k 1
  have htrans (k : Fin b) :
      ∀ᶠ N : ℕ in atTop,
        (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
          pkgB2_translationLength MS T J0 gap k N := by
    simpa [pkgB2_translationLength] using
      (pkgB2_translationLength_ge_blockScale_pow MS B T J0 gap hgap hJ0 k 1)
  have hshiftAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
        pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hshift k)
    simpa using h
  have htransAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
        pkgB2_translationLength MS T J0 gap k N := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => htrans k)
    simpa using h
  filter_upwards [hshiftAll, htransAll] with N hshiftN htransN
  intro p hpGood
  refine ⟨hpGood, ?_, ?_⟩
  · intro k
    have hactual := pkgB2_shiftLengthFloor_le_actual MS T J0 gap hJ0 N
      (fun k => pkgB2_repPrimeProject hT p k) hpGood k
    have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale]
      omega
    have hfloor : 0 <
        pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
      have hk := hshiftN k
      have hk' : pkgB2_blockScale MS.core.parameters B N ≤
          pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
        simpa only [pow_one] using hk
      exact lt_of_lt_of_le (Nat.zero_lt_one.trans_le hV) hk'
    change 0 < (T k).length (corrScales MS) (gap k) (J0 k) N
      (pkgB2_repPrimeProject hT p k)
    exact lt_of_lt_of_le hfloor hactual
  · intro k
    have hk := htransN k
    have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale]
      omega
    have hk' : pkgB2_blockScale MS.core.parameters B N ≤
        pkgB2_translationLength MS T J0 gap k N := by
      simpa only [pow_one] using hk
    exact lt_of_lt_of_le (Nat.zero_lt_one.trans_le hV) hk'

noncomputable def pkgB2_baseCoordinateLaw {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (c : pkgB2_Coord T) (z : ℤ) : ℝ :=
  match c with
  | .inl (.inl _) => harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1)) z
  | .inl (.inr ⟨k, (j, side)⟩) =>
      FromArithmetic.uniformIntegerIntervalLaw 0
        (pkgB2_shiftLength MS T J0 gap hT N p k) z
  | .inr (r, side) =>
      FromArithmetic.uniformIntegerIntervalLaw 0
        (pkgB2_translationLength MS T J0 gap r.1 N) z

noncomputable def pkgB2_baseMass {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) : ℝ :=
  if hreg : pkgB2_baseRegular MS B T J0 gap hT N p then
    ∏ i, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) (x i)
  else if x = 0 then 1 else 0

noncomputable def pkgB2_baseUpper {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) : ℕ :=
  (MS.core.parameters.X N B.1) ^ 2 +
    ∑ k : Fin b, pkgB2_shiftLength MS T J0 gap hT N p k +
    ∑ r : pkgB2_Nonroot T, pkgB2_translationLength MS T J0 gap r.1 N

noncomputable def pkgB2_baseWindow {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) : Finset ℤ :=
  Finset.Icc 0 (pkgB2_baseUpper MS B T J0 gap hT N p : ℤ)

theorem pkgB2_baseCoordinateLaw_nonneg {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (c : pkgB2_Coord T) (z : ℤ) :
    0 ≤ pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c z := by
  cases c with
  | inl old =>
      cases old with
      | inl u =>
          have hW : 0 < primorial (N + 1) := primorial_pos _
          have hnorm : 0 < harmonicNormalizer (MS.core.parameters.X N B.1)
              (primorial (N + 1)) :=
            harmonicNormalizer_pos_of_cutoff _ _ hW (MS.gapStage.valid_raw_cutoffs N B.1)
          exact pkgTest_harmonicLaw_nonneg_of_normalizer_pos
            (MS.core.parameters.Xpos N B.1) hnorm z
      | inr idx =>
          rcases idx with ⟨k, ⟨j, side⟩⟩
          simp only [pkgB2_baseCoordinateLaw]
          unfold FromArithmetic.uniformIntegerIntervalLaw
          split_ifs <;> positivity
  | inr idx =>
      rcases idx with ⟨r, side⟩
      simp only [pkgB2_baseCoordinateLaw]
      unfold FromArithmetic.uniformIntegerIntervalLaw
      split_ifs <;> positivity

theorem pkgB2_baseCoordinateLaw_tsum_one {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (c : pkgB2_Coord T) :
    ∑' z : ℤ, pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c z = 1 := by
  rcases hreg with ⟨hgood, hlength, htrans⟩
  cases c with
  | inl old =>
      cases old with
      | inl u =>
          have hW : 0 < primorial (N + 1) := primorial_pos _
          have hnorm : 0 < harmonicNormalizer (MS.core.parameters.X N B.1)
              (primorial (N + 1)) :=
            harmonicNormalizer_pos_of_cutoff _ _ hW (MS.gapStage.valid_raw_cutoffs N B.1)
          simpa [pkgB2_baseCoordinateLaw] using harmonicLaw_tsum_one
            (MS.core.parameters.Xpos N B.1) hnorm
      | inr idx =>
          rcases idx with ⟨k, ⟨j, side⟩⟩
          simpa [pkgB2_baseCoordinateLaw] using
            uniformIntegerIntervalLaw_tsum_one (hlength k)
  | inr idx =>
      rcases idx with ⟨r, side⟩
      simpa [pkgB2_baseCoordinateLaw] using
        uniformIntegerIntervalLaw_tsum_one (htrans r.1)

theorem pkgB2_baseCoordinateLaw_zero_outside {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (c : pkgB2_Coord T) (z : ℤ)
    (hz : z ∉ pkgB2_baseWindow MS B T J0 gap hT N p) :
    pkgB2_baseCoordinateLaw MS B T J0 gap hT N p c z = 0 := by
  cases c with
  | inl old =>
      cases old with
      | inl u =>
          by_contra hne
          have hsupp := harmonicLaw_nonzero_support hne
          have hXle : (MS.core.parameters.X N B.1) ^ 2 ≤
              pkgB2_baseUpper MS B T J0 gap hT N p := by
            dsimp [pkgB2_baseUpper]
            omega
          have hupper : z < (pkgB2_baseUpper MS B T J0 gap hT N p : ℤ) := by
            have hlt : z < ((MS.core.parameters.X N B.1) ^ 2 : ℤ) := hsupp.2.2
            exact hlt.trans_le (by exact_mod_cast hXle)
          exact hz (Finset.mem_Icc.mpr ⟨hsupp.1, hupper.le⟩)
      | inr idx =>
          rcases idx with ⟨k, ⟨j, side⟩⟩
          have hL : pkgB2_shiftLength MS T J0 gap hT N p k ≤
              pkgB2_baseUpper MS B T J0 gap hT N p := by
            dsimp [pkgB2_baseUpper]
            calc
              _ ≤ ∑ k' : Fin b, pkgB2_shiftLength MS T J0 gap hT N p k' :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                  (Finset.mem_univ k)
              _ ≤ (MS.core.parameters.X N B.1) ^ 2 +
                    ∑ k' : Fin b, pkgB2_shiftLength MS T J0 gap hT N p k' :=
                Nat.le_add_left _ _
              _ ≤ (MS.core.parameters.X N B.1) ^ 2 +
                    ∑ k' : Fin b, pkgB2_shiftLength MS T J0 gap hT N p k' +
                    ∑ r : pkgB2_Nonroot T, pkgB2_translationLength MS T J0 gap r.1 N :=
                Nat.le_add_right _ _
          change FromArithmetic.uniformIntegerIntervalLaw 0
            (pkgB2_shiftLength MS T J0 gap hT N p k) z = 0
          unfold FromArithmetic.uniformIntegerIntervalLaw
          split_ifs with h
          · have hupper : z < (pkgB2_baseUpper MS B T J0 gap hT N p : ℤ) :=
              lt_of_lt_of_le h.2 (by exact_mod_cast (show 0 +
                pkgB2_shiftLength MS T J0 gap hT N p k ≤
                  pkgB2_baseUpper MS B T J0 gap hT N p by simpa using hL))
            exact False.elim (hz (Finset.mem_Icc.mpr ⟨h.1, hupper.le⟩))
          · rfl
  | inr idx =>
      rcases idx with ⟨r, side⟩
      have hL : pkgB2_translationLength MS T J0 gap r.1 N ≤
          pkgB2_baseUpper MS B T J0 gap hT N p := by
        dsimp [pkgB2_baseUpper]
        calc
          _ ≤ ∑ r' : pkgB2_Nonroot T, pkgB2_translationLength MS T J0 gap r'.1 N :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ r)
          _ ≤ (MS.core.parameters.X N B.1) ^ 2 +
                ∑ k : Fin b, pkgB2_shiftLength MS T J0 gap hT N p k +
                ∑ r' : pkgB2_Nonroot T, pkgB2_translationLength MS T J0 gap r'.1 N :=
            Nat.le_add_left _ _
      change FromArithmetic.uniformIntegerIntervalLaw 0
        (pkgB2_translationLength MS T J0 gap r.1 N) z = 0
      unfold FromArithmetic.uniformIntegerIntervalLaw
      split_ifs with h
      · have hupper : z < (pkgB2_baseUpper MS B T J0 gap hT N p : ℤ) :=
          lt_of_lt_of_le h.2 (by exact_mod_cast (show 0 +
            pkgB2_translationLength MS T J0 gap r.1 N ≤
              pkgB2_baseUpper MS B T J0 gap hT N p by simpa using hL))
        exact False.elim (hz (Finset.mem_Icc.mpr ⟨h.1, hupper.le⟩))
      · rfl




private theorem pkgB2_productMass_tsum_one {d : ℕ}
    (μ : Fin d → ℤ → ℝ) (win : Finset ℤ)
    (hzero : ∀ i z, z ∉ win → μ i z = 0)
    (hone : ∀ i, ∑' z : ℤ, μ i z = 1) :
    ∑' x : Fin d → ℤ, ∏ i, μ i (x i) = 1 := by
  classical
  let S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => win
  have hprodZero : ∀ x ∉ S, ∏ i : Fin d, μ i (x i) = 0 := by
    intro x hx
    have hx' : ¬ ∀ i : Fin d, x i ∈ win := by
      simpa [S, Fintype.mem_piFinset] using hx
    obtain ⟨i, hi⟩ := not_forall.mp hx'
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (x i) hi)
  have hfactor :
      (∑ x ∈ S, ∏ i : Fin d, μ i (x i)) =
        ∏ i : Fin d, ∑ z ∈ win, μ i z := by
    simpa [S] using Finset.sum_prod_piFinset win (fun i z => μ i z)
  have hlocal (i : Fin d) : ∑ z ∈ win, μ i z = 1 := by
    have hsum : (∑ z ∈ win, μ i z) = ∑' z : ℤ, μ i z :=
      (tsum_eq_sum (s := win) (fun z hz => hzero i z hz)).symm
    calc
      ∑ z ∈ win, μ i z = ∑' z : ℤ, μ i z := hsum
      _ = 1 := hone i
  calc
    _ = ∑ x ∈ S, ∏ i : Fin d, μ i (x i) := tsum_eq_sum (s := S) hprodZero
    _ = ∏ i : Fin d, ∑ z ∈ win, μ i z := hfactor
    _ = 1 := by simp_rw [hlocal]; simp

theorem pkgB2_baseMass_zero_outside {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ)
    (hx : x ∉ Fintype.piFinset
      (fun _ : Fin (Fintype.card (pkgB2_Coord T)) =>
        pkgB2_baseWindow MS B T J0 gap hT N p)) :
    pkgB2_baseMass MS B T J0 gap hT N p x = 0 := by
  classical
  by_cases hreg : pkgB2_baseRegular MS B T J0 gap hT N p
  · have hx' : ¬ ∀ i : Fin (Fintype.card (pkgB2_Coord T)),
        x i ∈ pkgB2_baseWindow MS B T J0 gap hT N p := by
      simpa only [Fintype.mem_piFinset] using hx
    obtain ⟨i, hi⟩ := not_forall.mp hx'
    have hcoord := pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) (x i) hi
    have hprod :
        ∏ i : Fin (Fintype.card (pkgB2_Coord T)),
          pkgB2_baseCoordinateLaw MS B T J0 gap hT N p
            (pkgB2_coordEnum T i) (x i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hcoord
    simpa [pkgB2_baseMass, hreg] using hprod
  · by_cases hx0 : x = 0
    · subst x
      have hzeroMem : (0 : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) ∈
          Fintype.piFinset (fun _ : Fin (Fintype.card (pkgB2_Coord T)) =>
            pkgB2_baseWindow MS B T J0 gap hT N p) := by
        rw [Fintype.mem_piFinset]
        intro i
        apply Finset.mem_Icc.mpr
        constructor
        · norm_num
        · change (0 : ℤ) ≤ (pkgB2_baseUpper MS B T J0 gap hT N p : ℤ)
          exact_mod_cast (Nat.zero_le (pkgB2_baseUpper MS B T J0 gap hT N p))
      exact False.elim (hx hzeroMem)
    · simp [pkgB2_baseMass, hreg, hx0]

theorem pkgB2_baseMass_tsum_one {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) :
    ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
      pkgB2_baseMass MS B T J0 gap hT N p x = 1 := by
  classical
  by_cases hreg : pkgB2_baseRegular MS B T J0 gap hT N p
  · let μ : Fin (Fintype.card (pkgB2_Coord T)) → ℤ → ℝ := fun i z =>
      pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T i) z
    let win := pkgB2_baseWindow MS B T J0 gap hT N p
    have hzero (i : Fin (Fintype.card (pkgB2_Coord T))) (z : ℤ) (hz : z ∉ win) :
        μ i z = 0 := by
      exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p
        (pkgB2_coordEnum T i) z (by simpa [win] using hz)
    have hone (i : Fin (Fintype.card (pkgB2_Coord T))) :
        ∑' z : ℤ, μ i z = 1 := by
      exact pkgB2_baseCoordinateLaw_tsum_one MS B T J0 gap hT N p hreg
        (pkgB2_coordEnum T i)
    have hprod := pkgB2_productMass_tsum_one μ win hzero hone
    simpa [pkgB2_baseMass, hreg, μ] using hprod
  · simp [pkgB2_baseMass, hreg]

private noncomputable def pkgB2_coordinateResidueLaw {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (pkgB2_Coord T))) (r : Fin modulus) : ℝ :=
  ∑' z : ℤ,
    pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T i) z *
      (if integerResidue modulus hmod z = r then 1 else 0)

private theorem pkgB2_baseResidueLaw_eq_product {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (r : Fin (Fintype.card (pkgB2_Coord T)) → Fin modulus) :
    baseResidueLaw modulus hmod (pkgB2_baseMass MS B T J0 gap hT N p) r =
      ∏ i, pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i (r i) := by
  classical
  let d := Fintype.card (pkgB2_Coord T)
  let win := pkgB2_baseWindow MS B T J0 gap hT N p
  let S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => win
  let f : Fin d → ℤ → ℝ := fun i z =>
    pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T i) z
  have hbaseZero : ∀ x ∉ S, pkgB2_baseMass MS B T J0 gap hT N p x = 0 := by
    intro x hx
    apply pkgB2_baseMass_zero_outside MS B T J0 gap hT N p x
    simpa [S, win] using hx
  have hcoordZero (i : Fin d) (z : ℤ) (hz : z ∉ win) : f i z = 0 := by
    exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) z (by simpa [win] using hz)
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
        pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i a := by
    have hzero : ∀ z : ℤ, z ∉ win →
        f i z * (if integerResidue modulus hmod z = a then (1 : ℝ) else 0) = 0 := by
      intro z hz
      rw [hcoordZero i z hz]
      simp
    symm
    exact tsum_eq_sum (s := win) hzero
  calc
    _ = ∑ x ∈ S,
          pkgB2_baseMass MS B T J0 gap hT N p x *
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
          have hmass : pkgB2_baseMass MS B T J0 gap hT N p x = ∏ i : Fin d, f i (x i) := by
            simp [pkgB2_baseMass, hreg, f, d]
          rw [hmass, hindicator, ← Finset.prod_mul_distrib]
    _ = ∏ i : Fin d, ∑ z ∈ win,
          f i z * (if integerResidue modulus hmod z = r i then (1 : ℝ) else 0) := by
          simpa [S] using (Finset.sum_prod_piFinset win
            (fun i z => f i z *
              (if integerResidue modulus hmod z = r i then (1 : ℝ) else 0)))
    _ = ∏ i, pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i (r i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hlocal i (r i)

private theorem pkgB2_uniformResidueLaw_sum_one {modulus : ℕ} (hmod : 0 < modulus) :
    ∑ r : Fin modulus, uniformResidueLaw modulus r = 1 := by
  unfold uniformResidueLaw
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul]
  have hmodReal : (0 : ℝ) < modulus := by exact_mod_cast hmod
  field_simp [ne_of_gt hmodReal]

private theorem pkgB2_coordinateResidueLaw_nonneg {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (pkgB2_Coord T))) (r : Fin modulus) :
    0 ≤ pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r := by
  unfold pkgB2_coordinateResidueLaw
  apply tsum_nonneg
  intro z
  exact mul_nonneg
    (pkgB2_baseCoordinateLaw_nonneg MS B T J0 gap hT N p (pkgB2_coordEnum T i) z)
    (by split_ifs <;> positivity)

private theorem pkgB2_coordinateResidueLaw_sum_one {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (pkgB2_Coord T))) :
    ∑ r : Fin modulus,
      pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r = 1 := by
  classical
  let win := pkgB2_baseWindow MS B T J0 gap hT N p
  let coord := pkgB2_baseCoordinateLaw MS B T J0 gap hT N p (pkgB2_coordEnum T i)
  have hcoordZero (z : ℤ) (hz : z ∉ win) : coord z = 0 := by
    exact pkgB2_baseCoordinateLaw_zero_outside MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) z (by simpa [win] using hz)
  have htermZero (r : Fin modulus) (z : ℤ) (hz : z ∉ win) :
      coord z * (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 0 := by
    rw [hcoordZero z hz]
    simp
  have hsum (r : Fin modulus) :
      pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r =
        ∑ z ∈ win, coord z * (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
    unfold pkgB2_coordinateResidueLaw
    exact tsum_eq_sum (s := win) (fun z hz => htermZero r z hz)
  have hpart (z : ℤ) :
      ∑ r : Fin modulus,
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 1 := by
    simp
  have htotal : ∑ z ∈ win, coord z = 1 := by
    have hzeroLaw : ∀ z : ℤ, z ∉ win → coord z = 0 := hcoordZero
    calc
      _ = ∑' z : ℤ, coord z := (tsum_eq_sum (s := win) hzeroLaw).symm
      _ = 1 := pkgB2_baseCoordinateLaw_tsum_one MS B T J0 gap hT N p hreg
        (pkgB2_coordEnum T i)
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

private theorem pkgB2_baseResidueL1_le_coordinate_errors {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (modulus : ℕ) (hmod : 0 < modulus)
    (δ : Fin (Fintype.card (pkgB2_Coord T)) → ℝ)
    (hδ : ∀ i, finiteL1
      (pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i)
      (uniformResidueLaw modulus) ≤ δ i) :
    finiteL1
      (baseResidueLaw modulus hmod (pkgB2_baseMass MS B T J0 gap hT N p))
      (uniformBaseResidueLaw modulus (Fintype.card (pkgB2_Coord T))) ≤
      ∑ i, δ i := by
  classical
  let d := Fintype.card (pkgB2_Coord T)
  let μ : Fin d → Fin modulus → ℝ := fun i r =>
    pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r
  let ν : Fin d → Fin modulus → ℝ := fun _ r => uniformResidueLaw modulus r
  have hμsum (i : Fin d) : ∑ r : Fin modulus, |μ i r| = 1 := by
    have hnonneg (r : Fin modulus) : 0 ≤ μ i r := by
      exact pkgB2_coordinateResidueLaw_nonneg MS B T J0 gap hT N p modulus hmod i r
    calc
      _ = ∑ r : Fin modulus, μ i r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_of_nonneg (hnonneg r)]
      _ = 1 := pkgB2_coordinateResidueLaw_sum_one MS B T J0 gap hT N p hreg
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
        exact pkgB2_uniformResidueLaw_sum_one hmod
  have hUniform (r : Fin d → Fin modulus) :
      uniformBaseResidueLaw modulus d r = ∏ i, ν i (r i) := by
    simp [uniformBaseResidueLaw, uniformResidueLaw, ν, d, div_pow]
  have hprodBound :
      finiteL1 (fun r : Fin d → Fin modulus => ∏ i, μ i (r i))
        (fun r => ∏ i, ν i (r i)) ≤
        ∑ i, finiteL1 (μ i) (ν i) := by
    have hmain := finite_product_l1_telescoping μ ν
    calc
      _ ≤ ∑ i, finiteL1 (μ i) (ν i) *
          ∏ j ∈ Finset.univ.erase i,
            max (∑ r, |μ j r|) (∑ r, |ν j r|) := hmain
      _ = ∑ i, finiteL1 (μ i) (ν i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp_rw [hμsum, hνsum]
        simp
  have hmeasure :
      baseResidueLaw modulus hmod (pkgB2_baseMass MS B T J0 gap hT N p) =
        fun r : Fin d → Fin modulus => ∏ i, μ i (r i) := by
    funext r
    exact pkgB2_baseResidueLaw_eq_product MS B T J0 gap hT N p hreg modulus hmod r
  have huniform : uniformBaseResidueLaw modulus d =
      fun r : Fin d → Fin modulus => ∏ i, ν i (r i) := by
    funext r
    exact hUniform r
  calc
    _ = finiteL1 (fun r : Fin d → Fin modulus => ∏ i, μ i (r i))
          (fun r => ∏ i, ν i (r i)) := by rw [hmeasure, huniform]
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) := hprodBound
    _ ≤ ∑ i, δ i := Finset.sum_le_sum fun i hi => by
          simpa [μ, ν] using hδ i

private theorem pkgB2_integerResidue_eq_toNat_mod {modulus : ℕ} (hmod : 0 < modulus)
    (z : ℤ) (hz : 0 ≤ z) :
    integerResidue modulus hmod z = ⟨z.toNat % modulus, Nat.mod_lt _ hmod⟩ := by
  apply Fin.ext
  simp only [integerResidue]
  have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  have hmodEq : z % (modulus : ℤ) = (z.toNat : ℤ) % (modulus : ℤ) :=
    congrArg (fun n : ℤ => n % (modulus : ℤ)) hcast.symm
  rw [hmodEq, ← Int.natCast_mod, Int.toNat_natCast]

private theorem pkgB2_integerResidue_eq_iff {modulus : ℕ} (hmod : 0 < modulus)
    (z : ℤ) (hz : 0 ≤ z) (r : Fin modulus) :
    integerResidue modulus hmod z = r ↔ z.toNat % modulus = r.val := by
  rw [pkgB2_integerResidue_eq_toNat_mod hmod z hz]
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    exact Fin.ext h

private theorem pkgB2_pivotSamplingHypotheses {K sl : ℕ} {As : Finset ℚ}
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

private theorem pkgB2_harmonicPivotResidueL1_bound {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N modulus : ℕ)
    (hmod : 0 < modulus) (hcop : Nat.Coprime modulus (primorial (N + 1))) :
    finiteL1
      (harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus)
      (uniformResidueLaw modulus) ≤
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus := by
  obtain ⟨hW, hX, hlog⟩ := pkgB2_pivotSamplingHypotheses MS B N
  have hsampling := FromArithmetic.lem_sampling
    (MS.core.parameters.X N B.1) (primorial (N + 1)) hW hX hlog
  exact hsampling.1.residue_total_mass hX hlog modulus hcop hmod

private theorem pkgB2_pivotCoordinateResidueLaw_eq_harmonic {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (pkgB2_Coord T)))
    (hi : pkgB2_coordEnum T i = Sum.inl (Sum.inl ())) (r : Fin modulus) :
    pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r =
      harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r := by
  classical
  unfold pkgB2_coordinateResidueLaw harmonicResidueLaw
  apply tsum_congr
  intro z
  have hcoord : pkgB2_baseCoordinateLaw MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) z =
        harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1)) z := by
    rw [hi]
    rfl
  rw [hcoord]
  by_cases hz : 0 ≤ z
  · by_cases hres : z.toNat % modulus = r.val
    · have hres' := (pkgB2_integerResidue_eq_iff hmod z hz r).mpr hres
      simp [hz, hres, hres']
    · have hres' : integerResidue modulus hmod z ≠ r := by
        intro h
        exact hres ((pkgB2_integerResidue_eq_iff hmod z hz r).mp h)
      simp [hz, hres, hres']
  · simp [hz, harmonicLaw]

private theorem pkgB2_pivotCoordinateResidueL1_bound {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (modulus : ℕ) (hmod : 0 < modulus)
    (i : Fin (Fintype.card (pkgB2_Coord T)))
    (hi : pkgB2_coordEnum T i = Sum.inl (Sum.inl ()))
    (hcop : Nat.Coprime modulus (primorial (N + 1))) :
    finiteL1
      (pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i)
      (uniformResidueLaw modulus) ≤
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus := by
  have hEq : (fun r : Fin modulus =>
      pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r) =
      fun r => harmonicResidueLaw
        (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r := by
    funext r
    exact pkgB2_pivotCoordinateResidueLaw_eq_harmonic
      MS B T J0 gap hT N p modulus hmod i hi r
  calc
    _ = finiteL1 (fun r : Fin modulus => harmonicResidueLaw
          (harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))) modulus r)
          (uniformResidueLaw modulus) := by
        unfold finiteL1
        apply Finset.sum_congr rfl
        intro r hr
        exact congrArg (fun x : ℝ => |x - uniformResidueLaw modulus r|)
          (congrFun hEq r)
    _ ≤ harmonicResidueError
          (MS.core.parameters.X N B.1) (primorial (N + 1)) modulus :=
        pkgB2_harmonicPivotResidueL1_bound MS B N modulus hmod hcop

private theorem pkgB2_uniformIntegerIntervalResidueLaw_eq_nat {L modulus : ℕ}
    (hL : 0 < L) (hmod : 0 < modulus) (r : Fin modulus) :
    (∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
      (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) =
      ∑ n ∈ Finset.range L,
        if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
  classical
  let I : Finset ℤ := Finset.Ico 0 (L : ℤ)
  have hzero (z : ℤ) (hz : z ∉ I) :
      FromArithmetic.uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) = 0 := by
    have hnot : ¬ (0 ≤ z ∧ z < (L : ℤ)) := by
      simpa [I, Finset.mem_Ico] using hz
    simp [FromArithmetic.uniformIntegerIntervalLaw, hnot]
  have hsum :
      (∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) =
      ∑ z ∈ I, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
    exact tsum_eq_sum (s := I) (fun z hz => hzero z hz)
  calc
    _ = ∑ z ∈ I, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
          (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := hsum
    _ = ∑ n ∈ Finset.range L,
          if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
          apply Finset.sum_bij (s := I) (t := Finset.range L)
            (f := fun z : ℤ => FromArithmetic.uniformIntegerIntervalLaw 0 L z *
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
            have hres := pkgB2_integerResidue_eq_toNat_mod hmod z hz0
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
              simp [FromArithmetic.uniformIntegerIntervalLaw, hz0, hzL, h, hr]
            · have hr : integerResidue modulus hmod z ≠ r := fun hr => h (hcond.mp hr)
              simp [FromArithmetic.uniformIntegerIntervalLaw, hz0, hzL, h, hr]

private theorem pkgB2_uniformIntervalResidueL1_bound {L modulus : ℕ}
    (hL : 0 < L) (hmod : 0 < modulus) :
    finiteL1
      (fun r : Fin modulus =>
        ∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
          (if integerResidue modulus hmod z = r then (1 : ℝ) else 0))
      (uniformResidueLaw modulus) ≤ 2 * (modulus : ℝ) / L := by
  have hEq : (fun r : Fin modulus =>
      ∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
        (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) =
      fun r => ∑ n ∈ Finset.range L,
        if n % modulus = r.val then 1 / (L : ℝ) else 0 := by
    funext r
    exact pkgB2_uniformIntegerIntervalResidueLaw_eq_nat hL hmod r
  calc
    _ = finiteL1 (fun r : Fin modulus => ∑ n ∈ Finset.range L,
          if n % modulus = r.val then 1 / (L : ℝ) else 0)
          (uniformResidueLaw modulus) := by
        unfold finiteL1
        apply Finset.sum_congr rfl
        intro r hr
        change |(∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z *
          (if integerResidue modulus hmod z = r then (1 : ℝ) else 0)) -
            uniformResidueLaw modulus r| =
          |(∑ n ∈ Finset.range L,
            if n % modulus = r.val then 1 / (L : ℝ) else 0) -
            uniformResidueLaw modulus r|
        exact congrArg (fun x : ℝ => |x - uniformResidueLaw modulus r|)
          (congrFun hEq r)
    _ = finiteL1 (fun r : Fin modulus => ∑ n ∈ Finset.Ico 0 (0 + L),
          if n % modulus = r.val then 1 / (L : ℝ) else 0)
          (uniformResidueLaw modulus) := by
        unfold finiteL1
        apply Finset.sum_congr rfl
        intro r hr
        simp
    _ ≤ 2 * (modulus : ℝ) / L := by
      simpa using FromArithmetic.uniform_interval_sampling_bounds 0 L modulus hL hmod

private theorem pkgB2_harmonicResidueError_mono {X W k K : ℕ} (hk : k ≤ K)
    (hden : 0 < (X : ℝ) * (Real.log (X : ℝ) - (W : ℝ) / X)) :
    harmonicResidueError X W k ≤ harmonicResidueError X W K := by
  unfold harmonicResidueError
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.add_le_add_right hk 1

noncomputable def pkgB2_baseCoordinateError {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (i : Fin (Fintype.card (pkgB2_Coord T))) : ℝ :=
  let q := Fintype.card (pkgB2_Occurrence T E)
  let V := pkgB2_blockScale MS.core.parameters B N
  match pkgB2_coordEnum T i with
  | .inl (.inl _) => harmonicResidueError
      (MS.core.parameters.X N B.1) (primorial (N + 1)) (V ^ q)
  | .inl (.inr ⟨k, (j, side)⟩) =>
      2 * (V ^ q : ℝ) /
        (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) : ℝ)
  | .inr (r, side) =>
      2 * (V ^ q : ℝ) /
        (max 1 (pkgB2_translationLength MS T J0 gap r.1 N) : ℝ)

theorem pkgB2_coordinateResidueL1_le_error {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (E : Finset (pkgB2_Nonroot T))
    (modulus : ℕ) (hmod : 0 < modulus) (hcop : Nat.Coprime modulus (primorial (N + 1)))
    (hmodle : modulus ≤ (pkgB2_blockScale MS.core.parameters B N) ^
      Fintype.card (pkgB2_Occurrence T E))
    (i : Fin (Fintype.card (pkgB2_Coord T))) :
    finiteL1
      (pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i)
      (uniformResidueLaw modulus) ≤ pkgB2_baseCoordinateError MS B T J0 gap hT E N i := by
  classical
  cases hcoord : pkgB2_coordEnum T i with
  | inl old =>
      cases old with
      | inl u =>
          have hPivot := pkgB2_pivotCoordinateResidueL1_bound
            MS B T J0 gap hT N p modulus hmod i hcoord hcop
          have hXpos : 0 < (MS.core.parameters.X N B.1 : ℝ) := by
            exact_mod_cast MS.core.parameters.Xpos N B.1
          have hlog := (pkgB2_pivotSamplingHypotheses MS B N).2.2
          have hden : 0 < (MS.core.parameters.X N B.1 : ℝ) *
              (Real.log (MS.core.parameters.X N B.1 : ℝ) -
                (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1) :=
            mul_pos hXpos (sub_pos.mpr hlog)
          have hmono := pkgB2_harmonicResidueError_mono
            hmodle hden
          simpa [pkgB2_baseCoordinateError, hcoord] using hPivot.trans hmono
      | inr idx =>
          rcases idx with ⟨k, ⟨j, side⟩⟩
          have hLpos := hreg.2.1 k
          let pType : (k : Fin b) → Fin (T k).q → ℕ :=
            fun k => pkgB2_repPrimeProject hT p k
          have hfloor := pkgB2_shiftLengthFloor_le_actual MS T J0 gap hJ0 N
            pType hreg.1 k
          have hmaxLe :
              max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) ≤
                pkgB2_shiftLength MS T J0 gap hT N p k := by
            exact max_le (Nat.one_le_iff_ne_zero.mpr hLpos.ne') hfloor
          have hEq :
              (fun r : Fin modulus =>
                pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i r) =
              fun r => ∑' z : ℤ,
                FromArithmetic.uniformIntegerIntervalLaw 0
                  (pkgB2_shiftLength MS T J0 gap hT N p k) z *
                  (if integerResidue modulus hmod z = r then (1 : ℝ) else 0) := by
            funext r
            unfold pkgB2_coordinateResidueLaw
            rw [hcoord]
            rfl
          have hIneq := pkgB2_uniformIntervalResidueL1_bound hLpos hmod
          have hQreal : (modulus : ℝ) ≤
              (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                Fintype.card (pkgB2_Occurrence T E) := by exact_mod_cast hmodle
          have hmaxPos : 0 <
              (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) : ℝ) := by
            exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
          have hmaxLeReal :
              (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) : ℝ) ≤
                (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ) := by exact_mod_cast hmaxLe
          have hratio : (modulus : ℝ) /
              (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ) ≤
              (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                Fintype.card (pkgB2_Occurrence T E) /
              (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) : ℝ) := by
            calc
              _ ≤ _ := div_le_div_of_nonneg_right hQreal (by exact_mod_cast hLpos.le)
              _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hmaxPos hmaxLeReal
          calc
            _ = finiteL1 (fun r : Fin modulus =>
                ∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0
                  (pkgB2_shiftLength MS T J0 gap hT N p k) z *
                  (if integerResidue modulus hmod z = r then (1 : ℝ) else 0))
                (uniformResidueLaw modulus) := by
                  unfold finiteL1
                  apply Finset.sum_congr rfl
                  intro r hr
                  exact congrArg (fun x : ℝ => |x - uniformResidueLaw modulus r|)
                    (congrFun hEq r)
            _ ≤ 2 * (modulus : ℝ) /
                (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ) := hIneq
            _ ≤ pkgB2_baseCoordinateError MS B T J0 gap hT E N i := by
                have hscaled : (2 : ℝ) *
                    ((modulus : ℝ) /
                      (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ)) ≤
                    (2 : ℝ) *
                      ((pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                        Fintype.card (pkgB2_Occurrence T E) /
                        (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k)
                          (J0 k) N) : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left hratio (by norm_num)
                have hmul :
                    2 * (modulus : ℝ) /
                        (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ) ≤
                      2 * (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                          Fintype.card (pkgB2_Occurrence T E) /
                        (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k)
                          (J0 k) N) : ℝ) := by
                  calc
                    _ = 2 * ((modulus : ℝ) /
                        (pkgB2_shiftLength MS T J0 gap hT N p k : ℝ)) := by ring
                    _ ≤ _ := hscaled
                    _ = _ := by ring
                simpa [pkgB2_baseCoordinateError, hcoord] using hmul
      
  | inr rowCoord =>
      rcases rowCoord with ⟨r, side⟩
      have hApos := hreg.2.2 r.1
      have hEq :
          (fun x : Fin modulus =>
            pkgB2_coordinateResidueLaw MS B T J0 gap hT N p modulus hmod i x) =
          fun x => ∑' z : ℤ,
            FromArithmetic.uniformIntegerIntervalLaw 0
              (pkgB2_translationLength MS T J0 gap r.1 N) z *
              (if integerResidue modulus hmod z = x then (1 : ℝ) else 0) := by
        funext x
        unfold pkgB2_coordinateResidueLaw
        rw [hcoord]
        rfl
      have hIneq := pkgB2_uniformIntervalResidueL1_bound hApos hmod
      have hQreal : (modulus : ℝ) ≤
          (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
            Fintype.card (pkgB2_Occurrence T E) := by exact_mod_cast hmodle
      have hAmax : max 1 (pkgB2_translationLength MS T J0 gap r.1 N) =
          pkgB2_translationLength MS T J0 gap r.1 N := by
        exact max_eq_right (Nat.one_le_iff_ne_zero.mpr hApos.ne')
      have hAmaxReal : (max 1 (pkgB2_translationLength MS T J0 gap r.1 N) : ℝ) =
          (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) := by
        exact_mod_cast hAmax
      have hratio : (modulus : ℝ) /
          (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) ≤
          (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
            Fintype.card (pkgB2_Occurrence T E) /
          (max 1 (pkgB2_translationLength MS T J0 gap r.1 N) : ℝ) := by
        rw [hAmaxReal]
        exact div_le_div_of_nonneg_right hQreal (by exact_mod_cast hApos.le)
      calc
        _ = finiteL1 (fun x : Fin modulus =>
            ∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0
              (pkgB2_translationLength MS T J0 gap r.1 N) z *
              (if integerResidue modulus hmod z = x then (1 : ℝ) else 0))
            (uniformResidueLaw modulus) := by
              unfold finiteL1
              apply Finset.sum_congr rfl
              intro x hx
              exact congrArg (fun y : ℝ => |y - uniformResidueLaw modulus x|)
                (congrFun hEq x)
        _ ≤ 2 * (modulus : ℝ) /
            (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) := hIneq
        _ ≤ pkgB2_baseCoordinateError MS B T J0 gap hT E N i := by
            have hscaled : (2 : ℝ) *
                ((modulus : ℝ) /
                  (pkgB2_translationLength MS T J0 gap r.1 N : ℝ)) ≤
                (2 : ℝ) *
                  ((pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                    Fintype.card (pkgB2_Occurrence T E) /
                    (pkgB2_translationLength MS T J0 gap r.1 N : ℝ)) := by
              have hratio' : (modulus : ℝ) /
                  (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) ≤
                (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                  Fintype.card (pkgB2_Occurrence T E) /
                  (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) := by
                simpa [hAmaxReal] using hratio
              exact mul_le_mul_of_nonneg_left hratio' (by norm_num)
            have hmul :
                2 * (modulus : ℝ) /
                    (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) ≤
                  2 * (pkgB2_blockScale MS.core.parameters B N : ℝ) ^
                      Fintype.card (pkgB2_Occurrence T E) /
                    (pkgB2_translationLength MS T J0 gap r.1 N : ℝ) := by
              calc
                _ = 2 * ((modulus : ℝ) /
                    (pkgB2_translationLength MS T J0 gap r.1 N : ℝ)) := by ring
                _ ≤ _ := hscaled
                _ = _ := by ring
            simpa [pkgB2_baseCoordinateError, hcoord, hAmaxReal] using hmul

/-! A single row's fresh divisor variables are the independent raw coordinates
belonging to the block tail. -/

private abbrev pkgB2_TailIndex (K : ℕ) (B : Block K) :=
  {j : Fin K // j ∈ B.2.val}

private noncomputable def pkgB2_tailEnum {K : ℕ} (B : Block K) :
    Fin (Fintype.card (pkgB2_TailIndex K B)) ≃ pkgB2_TailIndex K B :=
  (Fintype.equivFin _).symm

private noncomputable def pkgB2_tailDivisorTemplate {K : ℕ} (B : Block K) :
    DivisorTemplate K K := by
  let D := HindmanSumsProducts.tailDivisorTemplate B.2.val
  exact { arity := D.arity, arity_le := D.arity_le, cutoff := D.cutoff }

private theorem pkgB2_tailDivisorTemplate_law_eq {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ MS.core.parameters.X N i) :
    divisorTemplateLaw MS.core.parameters N (pkgB2_tailDivisorTemplate B) =
      parameterTailProductLaw MS.core.parameters N B.2.val := by
  funext σ
  have h := HindmanSumsProducts.parameterTailProductLaw_eq_divisorTemplateLaw
    MS.core.parameters N B.2.val hX
  calc
    divisorTemplateLaw MS.core.parameters N (pkgB2_tailDivisorTemplate B) σ =
        FromArithmetic.divisorTemplateLaw MS.core.parameters N
          (HindmanSumsProducts.tailDivisorTemplate B.2.val) σ := rfl
    _ = FromArithmetic.parameterTailProductLaw MS.core.parameters N B.2.val σ :=
      (congrFun h σ).symm
    _ = parameterTailProductLaw MS.core.parameters N B.2.val σ := rfl

private def pkgB2_unitDivisorTemplate (K : ℕ) : DivisorTemplate K K :=
  { arity := 0, arity_le := Nat.zero_le K, cutoff := Fin.elim0 }

private noncomputable def pkgB2_divisorFamily {K q : ℕ} (B : Block K)
    (U : Finset (Fin q)) : Fin q → DivisorTemplate K K := by
  classical
  exact fun u => if u ∈ U then pkgB2_tailDivisorTemplate B else pkgB2_unitDivisorTemplate K

private def pkgB2_harmonicNatSupport (X W : ℕ) : Finset ℕ :=
  (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)

private theorem pkgB2_harmonicNatLaw_zero_outside (X W n : ℕ)
    (hn : n ∉ pkgB2_harmonicNatSupport X W) : harmonicNatLaw X W n = 0 := by
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro h
    apply hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  simp [harmonicNatLaw, hnot]

private theorem pkgB2_harmonicNatLaw_nonneg (X W n : ℕ) :
    0 ≤ harmonicNatLaw X W n := by
  have hnorm : 0 ≤ harmonicNormalizer X W := by
    unfold harmonicNormalizer
    apply Finset.sum_nonneg
    intro m hm
    exact one_div_nonneg.mpr (Nat.cast_nonneg m)
  unfold harmonicNatLaw
  split_ifs <;> positivity

private theorem pkgB2_parameterTailProductLaw_tsum_one {K : ℕ}
    (A : Parameters K) (N : ℕ) (Tails : Finset (Fin K))
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) :
    ∑' σ : ℕ, parameterTailProductLaw A N Tails σ = 1 := by
  classical
  let W := primorial (N + 1)
  let S : Fin K → Finset ℕ := fun i => pkgB2_harmonicNatSupport (A.X N i) W
  let Tuples : Finset (Fin K → ℕ) := Fintype.piFinset S
  let prodTail : (Fin K → ℕ) → ℕ := fun t => ∏ j ∈ Tails, t j
  let weight : (Fin K → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (A.X N i) W (t i)
  have hweight_zero (t : Fin K → ℕ) (ht : t ∉ Tuples) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ : harmonicNatLaw (A.X N i) W (t i) = 0 :=
      pkgB2_harmonicNatLaw_zero_outside (A.X N i) W (t i) (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hweight_nonneg (t : Fin K → ℕ) : 0 ≤ weight t := by
    dsimp [weight]
    exact Finset.prod_nonneg fun i hi => pkgB2_harmonicNatLaw_nonneg _ _ _
  have hterm_zero_out (σ : ℕ) (t : Fin K → ℕ) (ht : t ∉ Tuples) :
      (if prodTail t = σ then (1 : ℝ) else 0) * weight t = 0 := by
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
      ∑ t ∈ Tuples, (if prodTail t = σ then (1 : ℝ) else 0) * weight t := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum (s := Tuples) (hterm_zero_out σ)]
  have hlocal (i : Fin K) : ∑ n ∈ S i, harmonicNatLaw (A.X N i) W n = 1 := by
    have hsum : (∑ n ∈ S i, harmonicNatLaw (A.X N i) W n) =
        ∑' n : ℕ, harmonicNatLaw (A.X N i) W n :=
      (tsum_eq_sum (s := S i) (fun n hn =>
        pkgB2_harmonicNatLaw_zero_outside (A.X N i) W n (by simpa [S] using hn))).symm
    rw [hsum]
    exact harmonicNatLaw_tsum_one (primorial_pos _) (hX i)
  have htuple : ∑ t ∈ Tuples, weight t = 1 := by
    calc
      ∑ t ∈ Tuples, weight t = ∏ i : Fin K, ∑ n ∈ S i,
          harmonicNatLaw (A.X N i) W n := by
            simpa [Tuples, weight] using
              (Finset.prod_univ_sum S (fun i n => harmonicNatLaw (A.X N i) W n)).symm
      _ = 1 := by simp_rw [hlocal]; simp
  rw [tsum_eq_sum (s := Tuples.image prodTail) hLawZero]
  calc
    (∑ σ ∈ Tuples.image prodTail, parameterTailProductLaw A N Tails σ) =
        ∑ σ ∈ Tuples.image prodTail,
          ∑ t ∈ Tuples, (if prodTail t = σ then (1 : ℝ) else 0) * weight t := by
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

private theorem pkgB2_divisorLaw_support_witness {K : ℕ} (A : Parameters K) (N : ℕ)
    (D : DivisorTemplate K K) (σ : ℕ)
    (hσ : divisorTemplateLaw A N D σ ≠ 0) :
    ∃ t : Fin D.arity → ℕ,
      (∏ i, t i) = σ ∧
      ∀ i, A.X N (D.cutoff i) ≤ t i ∧ t i < (A.X N (D.cutoff i)) ^ 2 ∧
        Nat.Coprime (t i) (primorial (N + 1)) := by
  classical
  let X : Fin D.arity → ℕ := fun i => A.X N (D.cutoff i)
  let S : Fin D.arity → Finset ℕ := fun i =>
    pkgB2_harmonicNatSupport (X i) (primorial (N + 1))
  let T : Finset (Fin D.arity → ℕ) := Fintype.piFinset S
  let weight : (Fin D.arity → ℕ) → ℝ := fun t =>
    ∏ i, harmonicNatLaw (X i) (primorial (N + 1)) (t i)
  let product : (Fin D.arity → ℕ) → ℕ := fun t => ∏ i, t i
  have hweight_zero (t : Fin D.arity → ℕ) (ht : t ∉ T) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hz : harmonicNatLaw (X i) (primorial (N + 1)) (t i) = 0 :=
      pkgB2_harmonicNatLaw_zero_outside (X i) (primorial (N + 1)) (t i)
        (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
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
    have hz : (if product t = σ then (1 : ℝ) else 0) * weight t = 0 := by
      simp [hneq]
    exact hterm hz
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
  refine ⟨t, hproduct, ?_⟩
  intro i
  simpa [X] using hraw i

private theorem pkgB2_tailProduct_bounds {K : ℕ} (A : Parameters K) (B : Block K)
    (N : ℕ) (t : Fin (Fintype.card (pkgB2_TailIndex K B)) → ℕ)
    (ht : ∀ i, A.X N (pkgB2_tailEnum B i).1 ≤ t i ∧
      t i < (A.X N (pkgB2_tailEnum B i).1) ^ 2) :
    1 ≤ ∏ i, t i ∧ ∏ i, t i ≤ pkgB2_blockScale A B N := by
  classical
  have hXone (j : pkgB2_TailIndex K B) : 1 ≤ A.X N j.1 :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (A.Xpos N j.1))
  have hone : 1 ≤ ∏ i, t i :=
    Finset.one_le_prod fun i _ => (hXone (pkgB2_tailEnum B i)).trans (ht i).1
  have hprod :
      (∏ i : Fin (Fintype.card (pkgB2_TailIndex K B)), (A.X N (pkgB2_tailEnum B i).1) ^ 2) =
        ∏ j : pkgB2_TailIndex K B, (A.X N j.1) ^ 2 :=
    Fintype.prod_equiv (pkgB2_tailEnum B) _ _ (fun i => rfl)
  have hsubtype :
      (∏ j : pkgB2_TailIndex K B, (A.X N j.1) ^ 2) =
        ∏ j ∈ B.2.val, (A.X N j) ^ 2 := by
    change (∏ j : {j : Fin K // j ∈ B.2.val}, (A.X N j.1) ^ 2) = _
    symm
    exact Finset.prod_subtype B.2.val (by intro j; rfl) (fun j => (A.X N j) ^ 2)
  have htprod :
      ∏ i : Fin (Fintype.card (pkgB2_TailIndex K B)), t i ≤
        ∏ i : Fin (Fintype.card (pkgB2_TailIndex K B)),
          (A.X N (pkgB2_tailEnum B i).1) ^ 2 :=
    Finset.prod_le_prod fun i _ => (ht i).2.le
  constructor
  · exact hone
  · calc
      ∏ i, t i ≤ ∏ i, (A.X N (pkgB2_tailEnum B i).1) ^ 2 := htprod
      _ = ∏ j ∈ B.2.val, (A.X N j) ^ 2 := hprod.trans hsubtype
      _ ≤ 2 + A.M N + ∏ j ∈ B.2.val, (A.X N j) ^ 2 := by omega
      _ = pkgB2_blockScale A B N := rfl

private theorem pkgB2_parameterTailProductLaw_support_witness {K : ℕ}
    (A : Parameters K) (N : ℕ) (Tails : Finset (Fin K)) (σ : ℕ)
    (hσ : parameterTailProductLaw A N Tails σ ≠ 0) :
    ∃ t : Fin K → ℕ,
      t ∈ Fintype.piFinset
        (fun i => pkgB2_harmonicNatSupport (A.X N i) (primorial (N + 1))) ∧
      (∏ i ∈ Tails, t i) = σ := by
  classical
  let W := primorial (N + 1)
  let S : Fin K → Finset ℕ := fun i => pkgB2_harmonicNatSupport (A.X N i) W
  let Tuples : Finset (Fin K → ℕ) := Fintype.piFinset S
  let prodTail : (Fin K → ℕ) → ℕ := fun t => ∏ j ∈ Tails, t j
  let weight : (Fin K → ℕ) → ℝ := fun t => ∏ i, harmonicNatLaw (A.X N i) W (t i)
  have hweight_zero (t : Fin K → ℕ) (ht : t ∉ Tuples) : weight t = 0 := by
    have hnot : ¬ ∀ i, t i ∈ S i := by
      intro hall
      exact ht (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hμ := pkgB2_harmonicNatLaw_zero_outside (A.X N i) W (t i)
      (by simpa [S] using hi)
    dsimp [weight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  have hterm_zero (t : Fin K → ℕ) (ht : t ∉ Tuples) :
      (if prodTail t = σ then (1 : ℝ) else 0) * weight t = 0 := by
    simp [hweight_zero t ht]
  have hLawEq : parameterTailProductLaw A N Tails σ =
      ∑ t ∈ Tuples, (if prodTail t = σ then (1 : ℝ) else 0) * weight t := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum (s := Tuples) hterm_zero]
  have hsum_ne :
      (∑ t ∈ Tuples, (if prodTail t = σ then (1 : ℝ) else 0) * weight t) ≠ 0 := by
    intro hz
    apply hσ
    rw [hLawEq, hz]
  have hterm_exists : ∃ t ∈ Tuples,
      (if prodTail t = σ then (1 : ℝ) else 0) * weight t ≠ 0 := by
    by_contra hnone
    have hzero : ∀ t ∈ Tuples,
        (if prodTail t = σ then (1 : ℝ) else 0) * weight t = 0 := by
      intro t ht
      by_contra hne
      exact hnone ⟨t, ht, hne⟩
    exact hsum_ne (Finset.sum_eq_zero hzero)
  obtain ⟨t, ht, hterm⟩ := hterm_exists
  have hprod : prodTail t = σ := by
    by_contra hneq
    apply hterm
    simp [hneq]
  refine ⟨t, ?_, ?_⟩
  · simpa [Tuples, S] using ht
  · exact hprod

private theorem pkgB2_parameterTailProductLaw_support_bounds {K : ℕ}
    (A : Parameters K) (B : Block K) (N σ : ℕ)
    (hσ : parameterTailProductLaw A N B.2.val σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ pkgB2_blockScale A B N ∧ Nat.Coprime σ (primorial (N + 1)) := by
  classical
  obtain ⟨t, ht, hprod⟩ :=
    pkgB2_parameterTailProductLaw_support_witness A N B.2.val σ hσ
  let tailTuple : Fin (Fintype.card (pkgB2_TailIndex K B)) → ℕ :=
    fun i => t (pkgB2_tailEnum B i).1
  have hraw (i : Fin (Fintype.card (pkgB2_TailIndex K B))) :
      A.X N (pkgB2_tailEnum B i).1 ≤ tailTuple i ∧
      tailTuple i < (A.X N (pkgB2_tailEnum B i).1) ^ 2 := by
    have hi : t (pkgB2_tailEnum B i).1 ∈
        pkgB2_harmonicNatSupport (A.X N (pkgB2_tailEnum B i).1) (primorial (N + 1)) :=
      Fintype.mem_piFinset.mp ht (pkgB2_tailEnum B i).1
    exact ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2⟩
  have hbound := pkgB2_tailProduct_bounds A B N tailTuple hraw
  have hprodEq : ∏ i, tailTuple i = ∏ j ∈ B.2.val, t j := by
    calc
      ∏ i, tailTuple i = ∏ j : pkgB2_TailIndex K B, t j.1 :=
        Fintype.prod_equiv (pkgB2_tailEnum B) _ _ (fun i => rfl)
      _ = ∏ j ∈ B.2.val, t j := by
        change (∏ j : {j : Fin K // j ∈ B.2.val}, t j.1) = _
        symm
        exact Finset.prod_subtype B.2.val (by intro j; rfl) (fun j => t j)
  have hcop : Nat.Coprime σ (primorial (N + 1)) := by
    rw [← hprod]
    apply Nat.coprime_prod_left_iff.mpr
    intro j hj
    have hj' : t j ∈ pkgB2_harmonicNatSupport (A.X N j) (primorial (N + 1)) :=
      Fintype.mem_piFinset.mp ht j
    exact (Finset.mem_filter.mp hj').2
  refine ⟨?_, ?_, hcop⟩
  · calc
      1 ≤ ∏ i, tailTuple i := hbound.1
      _ = ∏ j ∈ B.2.val, t j := hprodEq
      _ = σ := hprod
  · calc
      σ = ∏ j ∈ B.2.val, t j := hprod.symm
      _ = ∏ i, tailTuple i := hprodEq.symm
      _ ≤ pkgB2_blockScale A B N := hbound.2

private theorem pkgB2_nu_nonneg_le_blockScale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (N : ℕ) (y : ℤ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ MS.core.parameters.X N i) :
    0 ≤ nu MS.core.parameters N B y ∧
      nu MS.core.parameters N B y ≤ (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
  classical
  let Scoord : Fin K → Finset ℕ := fun i => pkgB2_harmonicNatSupport
    (MS.core.parameters.X N i) (primorial (N + 1))
  let Tuples : Finset (Fin K → ℕ) := Fintype.piFinset Scoord
  let prodTail : (Fin K → ℕ) → ℕ := fun t => ∏ j ∈ B.2.val, t j
  let S : Finset ℕ := Tuples.image prodTail
  let tailLaw : ℕ → ℝ := parameterTailProductLaw MS.core.parameters N B.2.val
  have hLawZero (σ : ℕ) (hσ : σ ∉ S) : tailLaw σ = 0 := by
    by_contra hne
    obtain ⟨t, ht, hprod⟩ :=
      pkgB2_parameterTailProductLaw_support_witness MS.core.parameters N B.2.val σ hne
    apply hσ
    exact Finset.mem_image.mpr ⟨t, ht, hprod⟩
  have hLawNonneg (σ : ℕ) : 0 ≤ tailLaw σ := by
    unfold tailLaw parameterTailProductLaw
    apply tsum_nonneg
    intro t
    have hw : 0 ≤ ∏ i, harmonicNatLaw (MS.core.parameters.X N i)
        (primorial (N + 1)) (t i) :=
      Finset.prod_nonneg fun i hi => pkgB2_harmonicNatLaw_nonneg _ _ _
    split_ifs <;> positivity
  have htotal : ∑' σ : ℕ, tailLaw σ = 1 :=
    pkgB2_parameterTailProductLaw_tsum_one MS.core.parameters N B.2.val hX
  have hsum : ∑ σ ∈ S, tailLaw σ = 1 := by
    have hz : ∀ σ ∉ S, tailLaw σ = 0 := hLawZero
    simpa [tailLaw] using (tsum_eq_sum (s := S) hz).symm.trans htotal
  have htermZero (σ : ℕ) (hσ : σ ∉ S) :
      tailLaw σ * (σ : ℝ) * (if (σ : ℤ) ∣ y then 1 else 0) = 0 := by
    simp [hLawZero σ hσ]
  unfold nu nuB
  rw [tsum_eq_sum (s := S) htermZero]
  constructor
  · apply Finset.sum_nonneg
    intro σ hσ
    exact mul_nonneg (mul_nonneg (hLawNonneg σ) (by positivity)) (by split_ifs <;> positivity)
  · have hpoint (σ : ℕ) (hσ : σ ∈ S) :
        tailLaw σ * (σ : ℝ) * (if (σ : ℤ) ∣ y then 1 else 0) ≤
          tailLaw σ * (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
      by_cases hdiv : (σ : ℤ) ∣ y
      · simp only [if_pos hdiv, mul_one]
        by_cases hlaw : tailLaw σ = 0
        · simp [hlaw]
        · have hbound := pkgB2_parameterTailProductLaw_support_bounds
            MS.core.parameters B N σ hlaw
          have hcast : (σ : ℝ) ≤ (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
            exact_mod_cast hbound.2.1
          exact mul_le_mul_of_nonneg_left hcast (hLawNonneg σ)
      · simp only [if_neg hdiv, mul_zero]
        exact mul_nonneg (hLawNonneg σ) (by positivity)
    calc
      _ ≤ ∑ σ ∈ S, tailLaw σ * (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact hpoint σ hσ
      _ = (∑ σ ∈ S, tailLaw σ) * (pkgB2_blockScale MS.core.parameters B N : ℝ) := by
        rw [Finset.sum_mul]
      _ = (pkgB2_blockScale MS.core.parameters B N : ℝ) := by rw [hsum, one_mul]

private theorem pkgB2_divisorFamily_support_specs {K sl q : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (U : Finset (Fin q)) (u : Fin q) (N σ : ℕ)
    (hσ : divisorTemplateLaw MS.core.parameters N (pkgB2_divisorFamily B U u) σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ pkgB2_blockScale MS.core.parameters B N ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  classical
  by_cases hactive : u ∈ U
  · have htail : divisorTemplateLaw MS.core.parameters N
        (pkgB2_tailDivisorTemplate B) σ ≠ 0 := by
      simpa [pkgB2_divisorFamily, hactive] using hσ
    have hLaw := pkgB2_tailDivisorTemplate_law_eq MS B N
      (MS.gapStage.valid_raw_cutoffs N)
    have htailLaw : parameterTailProductLaw MS.core.parameters N B.2.val σ ≠ 0 := by
      rw [← hLaw]
      exact htail
    have hspec := pkgB2_parameterTailProductLaw_support_bounds
      MS.core.parameters B N σ htailLaw
    exact ⟨hspec.1, hspec.2.1, hspec.2.2⟩
  · have hunit : divisorTemplateLaw MS.core.parameters N
        (pkgB2_unitDivisorTemplate K) σ ≠ 0 := by
      simpa [pkgB2_divisorFamily, hactive] using hσ
    obtain ⟨t, hprod, _⟩ := pkgB2_divisorLaw_support_witness
      MS.core.parameters N (pkgB2_unitDivisorTemplate K) σ hunit
    have hσone : σ = 1 := by
      calc
        σ = ∏ i : Fin 0, t i := hprod.symm
        _ = 1 := Fintype.prod_empty _
    constructor
    · rw [hσone]
    constructor
    · rw [hσone]
      dsimp [pkgB2_blockScale]
      omega
    · simpa [hσone]

private theorem pkgB2_divisorFamily_nuB {K sl q : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (U : Finset (Fin q)) (u : Fin q) (N : ℕ) (y : ℤ) :
    nuB (divisorTemplateLaw MS.core.parameters N (pkgB2_divisorFamily B U u)) y =
      if u ∈ U then nu MS.core.parameters N B y else 1 := by
  classical
  by_cases hu : u ∈ U
  · simp only [pkgB2_divisorFamily, if_pos hu]
    have hLaw := pkgB2_tailDivisorTemplate_law_eq MS B N
      (MS.gapStage.valid_raw_cutoffs N)
    have h := congrArg (fun L : ℕ → ℝ => nuB L y) hLaw
    simpa [nu] using h
  · let D0 : FromArithmetic.DivisorTemplate K K :=
      { arity := 0, arity_le := Nat.zero_le K, cutoff := Fin.elim0 }
    have hFrom : nuB (FromArithmetic.divisorTemplateLaw MS.core.parameters N D0) y = 1 :=
      HindmanSumsProducts.nuB_divisorTemplate_arity_zero
        MS.core.parameters N D0 rfl y
    have hLaw : divisorTemplateLaw MS.core.parameters N (pkgB2_unitDivisorTemplate K) =
        FromArithmetic.divisorTemplateLaw MS.core.parameters N D0 := by rfl
    have hunitNu :
        nuB (divisorTemplateLaw MS.core.parameters N (pkgB2_unitDivisorTemplate K)) y = 1 := by
      have hEq := congrArg (fun L : ℕ → ℝ => nuB L y) hLaw
      exact hEq.trans hFrom
    simpa [pkgB2_divisorFamily, hu] using hunitNu

private theorem pkgB2_momentPivotLog_dominates_gap_scale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (MS.core.parameters.X N B.1 : ℝ))
      (fun N => (pkgB2_momentGapScale MS l N : ℝ)) := by
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
      (MS.core.parameters.H N l : ℝ) / (pkgB2_momentGapScale MS l N : ℝ) ^ C ≤
        Real.log (MS.core.parameters.X N B.1 : ℝ) /
          (pkgB2_momentGapScale MS l N : ℝ) ^ C := by
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
      (pkgB2_momentGapScale MS l N : ℝ) ^ C := by
    simpa [pkgB2_momentGapScale] using hN
  exact hN'.trans hcmp

private theorem pkgB2_momentPivotCutoff_dominates_gap_scale {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) :
    OAI.MicrocellScale.Dominates
      (fun N => (MS.core.parameters.X N B.1 : ℝ))
      (fun N => (pkgB2_momentGapScale MS l N : ℝ)) := by
  intro C hC
  let G : ℕ → ℕ := fun N => pkgB2_momentGapScale MS l N
  let S : ℕ → ℝ := fun N => (G N : ℝ)
  have hS : Tendsto S atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (pkgB2_momentGapScale_tendsto MS l)
  have hlogDom := pkgB2_momentPivotLog_dominates_gap_scale MS B l hgap
  have hlogRatio := hlogDom (C + 1) (by linarith)
  have hSpos (N : ℕ) : 0 < S N := by
    have hNat : 0 < G N := by
      dsimp [G, pkgB2_momentGapScale]
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


private theorem pkgB2_momentPivotLogDen_ge_half {K sl : ℕ} {As : Finset ℚ}
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

private theorem pkgB2_pivotResidueError_superPolynomial {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hgap : ValidGap B l) (q : ℕ) :
    SuperPolynomialSmall
      (fun N => harmonicResidueError (MS.core.parameters.X N B.1)
        (primorial (N + 1)) ((masterScaleV MS.core.parameters N l) ^
          q))
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)) := by
  intro C hC
  let rows := q
  let G : ℕ → ℕ := fun N => pkgB2_momentGapScale MS l N
  let S : ℕ → ℝ := fun N => (G N : ℝ)
  let V : ℕ → ℕ := fun N => masterScaleV MS.core.parameters N l
  let Aexp : ℝ := ((rows + 1 : ℕ) : ℝ) + C
  have hAexp : 0 < Aexp := by dsimp [Aexp]; positivity
  have hS_tendsto : Tendsto S atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (pkgB2_momentGapScale_tendsto MS l)
  have hSpos (N : ℕ) : 0 < S N := by
    have hNat : 0 < G N := by
      dsimp [G, pkgB2_momentGapScale]
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
    dsimp [V, S, pkgB2_momentGapScale]
    exact_mod_cast Nat.le_add_left (masterScaleV MS.core.parameters N l)
      ((MS.primeStage.pool N l).upper)
  have hXratio := pkgB2_momentPivotCutoff_dominates_gap_scale MS B l hgap
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
    have hDen := pkgB2_momentPivotLogDen_ge_half MS B N
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
      have hVle : V N ≤ pkgB2_momentGapScale MS l N := by
        dsimp [V, pkgB2_momentGapScale]
        omega
      have hcast := (Real.rpow_natCast (V N : ℝ) (rows + 1)).symm
      rw [hcast]
      have hVleReal : (V N : ℝ) ≤ S N := by
        change (V N : ℝ) ≤ (pkgB2_momentGapScale MS l N : ℝ)
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
      mul_pos hXposN (by linarith [pkgB2_momentPivotLogDen_ge_half MS B N])
    have hVnonneg : 0 ≤ (V N : ℝ) := by positivity
    unfold harmonicResidueError
    exact mul_nonneg (div_nonneg (by positivity) hdenN.le)
      (Real.rpow_nonneg hVnonneg C)
  exact squeeze_zero' (Eventually.of_forall hErrNonneg) hSmallBound hTop

private theorem pkgB2_superPolynomialSmall_scale_transfer {e V S : ℕ → ℝ}
    (hVleS : ∀ N, V N ≤ S N)
    (hVnonneg : ∀ N, 0 ≤ V N)
    (heNonneg : ∀ N, 0 ≤ e N)
    (hsmall : SuperPolynomialSmall e S) :
    SuperPolynomialSmall e V := by
  intro C hC
  have htop := hsmall C hC
  have hupper : ∀ᶠ N : ℕ in atTop, e N * V N ^ C ≤ e N * S N ^ C := by
    filter_upwards with N
    apply mul_le_mul_of_nonneg_left _ (heNonneg N)
    exact Real.rpow_le_rpow (hVnonneg N) (hVleS N) hC.le
  have hnonneg (N : ℕ) : 0 ≤ e N * V N ^ C :=
    mul_nonneg (heNonneg N) (Real.rpow_nonneg (hVnonneg N) C)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper htop

private theorem pkgB2_pivotBlockError_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (l : Fin K) (hgap : ValidGap B l)
    (T : Fin b → CubeTemplate) (E : Finset (pkgB2_Nonroot T)) :
    SuperPolynomialSmall
      (fun N => harmonicResidueError (MS.core.parameters.X N B.1)
        (primorial (N + 1))
        ((pkgB2_blockScale MS.core.parameters B N) ^
          Fintype.card (pkgB2_Occurrence T E)))
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  let q := Fintype.card (pkgB2_Occurrence T E)
  let V : ℕ → ℕ := fun N => pkgB2_blockScale MS.core.parameters B N
  let S : ℕ → ℝ := fun N => (masterScaleV MS.core.parameters N l : ℝ)
  have hsmall : SuperPolynomialSmall
      (fun N => harmonicResidueError (MS.core.parameters.X N B.1)
        (primorial (N + 1)) ((masterScaleV MS.core.parameters N l) ^ q)) S := by
    simpa [S, q] using pkgB2_pivotResidueError_superPolynomial MS B l hgap q
  have hVleS (N : ℕ) : (V N : ℝ) ≤ S N := by
    change (pkgB2_blockScale MS.core.parameters B N : ℝ) ≤
      (masterScaleV MS.core.parameters N l : ℝ)
    exact_mod_cast pkgB2_blockScale_le_masterScaleV MS.core.parameters B l hgap.1 N
  have hbigNonneg (N : ℕ) :
      0 ≤ harmonicResidueError (MS.core.parameters.X N B.1)
        (primorial (N + 1)) ((masterScaleV MS.core.parameters N l) ^ q) := by
    have hXpos : 0 < (MS.core.parameters.X N B.1 : ℝ) := by
      exact_mod_cast MS.core.parameters.Xpos N B.1
    have hden : 0 < (MS.core.parameters.X N B.1 : ℝ) *
        (Real.log (MS.core.parameters.X N B.1 : ℝ) -
          (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1) := by
      have hlog := pkgB2_momentPivotLogDen_ge_half MS B N
      exact mul_pos hXpos (by linarith)
    unfold harmonicResidueError
    exact div_nonneg (by positivity) hden.le
  have hsmallV := pkgB2_superPolynomialSmall_scale_transfer
    (e := fun N => harmonicResidueError (MS.core.parameters.X N B.1)
      (primorial (N + 1)) ((masterScaleV MS.core.parameters N l) ^ q))
    (V := fun N => (V N : ℝ)) (S := S) hVleS (fun _ => by positivity)
    hbigNonneg hsmall
  intro C hC
  have htop := hsmallV C hC
  have hmodle (N : ℕ) : V N ^ q ≤ masterScaleV MS.core.parameters N l ^ q :=
    Nat.pow_le_pow_left
      (pkgB2_blockScale_le_masterScaleV MS.core.parameters B l hgap.1 N) q
  have hdenPos (N : ℕ) :
      0 < (MS.core.parameters.X N B.1 : ℝ) *
        (Real.log (MS.core.parameters.X N B.1 : ℝ) -
          (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1) := by
    have hXpos : 0 < (MS.core.parameters.X N B.1 : ℝ) := by
      exact_mod_cast MS.core.parameters.Xpos N B.1
    have hlog := pkgB2_momentPivotLogDen_ge_half MS B N
    exact mul_pos hXpos (by linarith)
  have herror (N : ℕ) :
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) (V N ^ q) ≤
        harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1))
          (masterScaleV MS.core.parameters N l ^ q) :=
    pkgB2_harmonicResidueError_mono (hmodle N) (hdenPos N)
  have hupper : ∀ᶠ N : ℕ in atTop,
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1)) (V N ^ q) *
        (V N : ℝ) ^ C ≤
      harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1))
        (masterScaleV MS.core.parameters N l ^ q) * (V N : ℝ) ^ C := by
    filter_upwards with N
    exact mul_le_mul_of_nonneg_right (herror N)
      (Real.rpow_nonneg (by positivity) C)
  have hnonneg (N : ℕ) :
      0 ≤ harmonicResidueError (MS.core.parameters.X N B.1) (primorial (N + 1))
        (V N ^ q) * (V N : ℝ) ^ C := by
    unfold harmonicResidueError
    exact mul_nonneg
      (div_nonneg (by positivity) (hdenPos N).le)
      (Real.rpow_nonneg (by positivity) C)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper htop

private theorem pkgB2_intervalError_superPolynomial {q : ℕ}
    (V L : ℕ → ℕ) (hVtendsto : Tendsto (fun N => (V N : ℝ)) atTop atTop)
    (hVone : ∀ N, 1 ≤ V N)
    (hFloor : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, V N ^ m ≤ max 1 (L N)) :
    SuperPolynomialSmall
      (fun N => 2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ))
      (fun N => (V N : ℝ)) := by
  intro C hC
  let S : ℕ → ℝ := fun N => (V N : ℝ)
  let Aexp : ℝ := (q : ℝ) + C
  let m : ℕ := Nat.ceil (Aexp + 1)
  have hApos : 0 < Aexp := by dsimp [Aexp]; positivity
  have hm : Aexp + 1 ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil (Aexp + 1)
  have hS : Tendsto S atTop atTop := hVtendsto
  have hSpos (N : ℕ) : 0 < S N := by
    change (0 : ℝ) < (V N : ℝ)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hVone N))
  have hSone (N : ℕ) : 1 ≤ S N := by
    change (1 : ℝ) ≤ (V N : ℝ)
    exact_mod_cast hVone N
  have hFloorLower : ∀ᶠ N : ℕ in atTop,
      S N ^ (m : ℝ) ≤ (max 1 (L N) : ℝ) := by
    filter_upwards [hFloor m] with N hN
    have hcast : ((V N) ^ m : ℝ) = S N ^ (m : ℝ) := by
      dsimp [S]
      exact (Real.rpow_natCast (V N : ℝ) m).symm
    rw [← hcast]
    exact_mod_cast hN
  have hProduct (N : ℕ) :
      ((V N : ℝ) ^ q) * (V N : ℝ) ^ C ≤ S N ^ Aexp := by
    calc
      _ = S N ^ (q : ℝ) * S N ^ C := by
        simp [S, Real.rpow_natCast]
      _ = S N ^ ((q : ℝ) + C) := (Real.rpow_add (hSpos N) _ _).symm
      _ ≤ S N ^ Aexp := by
        change S N ^ ((q : ℝ) + C) ≤ S N ^ ((q : ℝ) + C)
        exact le_rfl
  have hSmallBound : ∀ᶠ N : ℕ in atTop,
      (2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ)) * (V N : ℝ) ^ C ≤ 2 / S N := by
    filter_upwards [hFloorLower] with N hfloor
    have hDenPos : 0 < (max 1 (L N) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (L N)))
    have hratio : S N ^ Aexp / (max 1 (L N) : ℝ) ≤ 1 / S N := by
      apply (div_le_div_iff₀ hDenPos (hSpos N)).2
      calc
        S N ^ Aexp * S N = S N ^ (Aexp + 1) := by
          calc
            _ = S N ^ Aexp * S N ^ (1 : ℝ) := by simp
            _ = _ := (Real.rpow_add (hSpos N) Aexp 1).symm
        _ ≤ S N ^ (m : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (hSone N) hm
        _ ≤ (max 1 (L N) : ℝ) := hfloor
        _ = 1 * (max 1 (L N) : ℝ) := by ring
    calc
      _ = 2 * ((((V N : ℝ) ^ q) * (V N : ℝ) ^ C) /
          (max 1 (L N) : ℝ)) := by ring
      _ ≤ 2 * (S N ^ Aexp / (max 1 (L N) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right (hProduct N) (by positivity)
      _ ≤ 2 / S N := by
        have hmul := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
        simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hInv : Tendsto (fun N : ℕ => (S N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hS
  have hTop : Tendsto (fun N : ℕ => 2 / S N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hInv
  have hnonneg (N : ℕ) :
      0 ≤ (2 * ((V N) ^ q : ℝ) / (max 1 (L N) : ℝ)) * (V N : ℝ) ^ C := by
    positivity
  exact squeeze_zero' (Eventually.of_forall hnonneg) hSmallBound hTop

private theorem pkgB2_blockScale_tendsto {K : ℕ} (A : Parameters K) (B : Block K) :
    Tendsto (fun N => pkgB2_blockScale A B N) atTop atTop := by
  have hbound (N : ℕ) : N ≤ pkgB2_blockScale A B N := by
    dsimp [pkgB2_blockScale]
    calc
      N ≤ primorial (N + 1) := Nat.le_trans (Nat.le_succ N) le_primorial_self
      _ ≤ A.M N := A.Wle N
      _ ≤ 2 + A.M N + ∏ j ∈ B.2.val, (A.X N j) ^ 2 := by omega
  rw [tendsto_atTop]
  intro n
  filter_upwards [eventually_ge_atTop n] with N hN
  exact hN.trans (hbound N)

private theorem pkgB2_shiftError_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (k : Fin b) (q : ℕ) :
    SuperPolynomialSmall
      (fun N => 2 * ((pkgB2_blockScale MS.core.parameters B N) ^ q : ℝ) /
        (max 1 (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k) N) : ℝ))
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  apply pkgB2_intervalError_superPolynomial (q := q)
    (pkgB2_blockScale MS.core.parameters B)
    (pkgB2_momentShiftLengthLower MS (gap k) (T k) (J0 k))
    (by
      change Tendsto ((fun n : ℕ => (n : ℝ)) ∘
        pkgB2_blockScale MS.core.parameters B) atTop atTop
      exact tendsto_natCast_atTop_atTop.comp
        (pkgB2_blockScale_tendsto MS.core.parameters B))
    (fun N => by
      exact_mod_cast (show 1 ≤ pkgB2_blockScale MS.core.parameters B N by
        dsimp [pkgB2_blockScale]; omega))
    (fun m => by
      have hfloor := pkgB2_shiftLengthFloor_ge_blockScale_pow
        MS B T J0 gap hgap hJ0 k m
      filter_upwards [hfloor] with N hN
      exact le_trans hN (Nat.le_max_right 1 _))

private theorem pkgB2_translationError_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (k : Fin b) (q : ℕ) :
    SuperPolynomialSmall
      (fun N => 2 * ((pkgB2_blockScale MS.core.parameters B N) ^ q : ℝ) /
        (max 1 (pkgB2_translationLength MS T J0 gap k N) : ℝ))
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  apply pkgB2_intervalError_superPolynomial (q := q)
    (pkgB2_blockScale MS.core.parameters B)
    (pkgB2_translationLength MS T J0 gap k)
    (by
      change Tendsto ((fun n : ℕ => (n : ℝ)) ∘
        pkgB2_blockScale MS.core.parameters B) atTop atTop
      exact tendsto_natCast_atTop_atTop.comp
        (pkgB2_blockScale_tendsto MS.core.parameters B))
    (fun N => by
      exact_mod_cast (show 1 ≤ pkgB2_blockScale MS.core.parameters B N by
        dsimp [pkgB2_blockScale]; omega))
    (fun m => by
      have hfloor := pkgB2_translationLength_ge_blockScale_pow
        MS B T J0 gap hgap hJ0 k m
      filter_upwards [hfloor] with N hN
      exact le_trans hN (Nat.le_max_right 1 _))

private noncomputable def pkgB2_epsilonBase {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card (pkgB2_Coord T)),
    pkgB2_baseCoordinateError MS B T J0 gap hT E N i

private theorem pkgB2_epsilonBase_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (hT : ∀ k, Allowed Dm (T k))
    (l : Fin K) (hl : ValidGap B l) (E : Finset (pkgB2_Nonroot T)) :
    SuperPolynomialSmall (pkgB2_epsilonBase MS B T J0 gap hT E)
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  classical
  let V : ℕ → ℝ := fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)
  have hcoord (i : Fin (Fintype.card (pkgB2_Coord T))) :
      SuperPolynomialSmall
        (fun N => pkgB2_baseCoordinateError MS B T J0 gap hT E N i) V := by
    cases hci : pkgB2_coordEnum T i with
    | inl old =>
        cases old with
        | inl _ =>
            simpa [pkgB2_baseCoordinateError, hci, V] using
              (pkgB2_pivotBlockError_superPolynomial MS B l hl T E)
        | inr idx =>
            rcases idx with ⟨k, ⟨j, side⟩⟩
            simpa [pkgB2_baseCoordinateError, hci, V] using
              (pkgB2_shiftError_superPolynomial MS B T J0 gap hgap hJ0 k
                (Fintype.card (pkgB2_Occurrence T E)))
    | inr idx =>
        rcases idx with ⟨r, side⟩
        simpa [pkgB2_baseCoordinateError, hci, V] using
          (pkgB2_translationError_superPolynomial MS B T J0 gap hgap hJ0 r.1
            (Fintype.card (pkgB2_Occurrence T E)))
  intro C hC
  have hterm (i : Fin (Fintype.card (pkgB2_Coord T))) :
      Tendsto (fun N =>
        pkgB2_baseCoordinateError MS B T J0 gap hT E N i * V N ^ C)
        atTop (𝓝 0) := hcoord i C hC
  have hsum : Tendsto
      (fun N => ∑ i : Fin (Fintype.card (pkgB2_Coord T)),
        pkgB2_baseCoordinateError MS B T J0 gap hT E N i * V N ^ C)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum
      (Finset.univ : Finset (Fin (Fintype.card (pkgB2_Coord T))))
      (fun i hi => hterm i)
  have hEq (N : ℕ) : pkgB2_epsilonBase MS B T J0 gap hT E N * V N ^ C =
      ∑ i : Fin (Fintype.card (pkgB2_Coord T)),
        pkgB2_baseCoordinateError MS B T J0 gap hT E N i * V N ^ C := by
    simp [pkgB2_epsilonBase, V, Finset.sum_mul]
  apply hsum.congr'
  filter_upwards with N
  exact (hEq N).symm


private theorem pkgB2_baseCoordinateError_nonneg {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (i : Fin (Fintype.card (pkgB2_Coord T))) :
    0 ≤ pkgB2_baseCoordinateError MS B T J0 gap hT E N i := by
  classical
  cases hcoord : pkgB2_coordEnum T i with
  | inl old =>
      cases old with
      | inl u =>
          have hXpos : 0 < (MS.core.parameters.X N B.1 : ℝ) := by
            exact_mod_cast MS.core.parameters.Xpos N B.1
          have hlog := (pkgB2_pivotSamplingHypotheses MS B N).2.2
          have hden : 0 < (MS.core.parameters.X N B.1 : ℝ) *
              (Real.log (MS.core.parameters.X N B.1 : ℝ) -
                (primorial (N + 1) : ℝ) / MS.core.parameters.X N B.1) :=
            mul_pos hXpos (sub_pos.mpr hlog)
          simp [pkgB2_baseCoordinateError, hcoord, harmonicResidueError]
          positivity
      | inr idx =>
          simp [pkgB2_baseCoordinateError, hcoord]
          positivity
  | inr idx =>
      simp [pkgB2_baseCoordinateError, hcoord]
      positivity

private theorem pkgB2_epsilonBase_nonneg {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) :
    0 ≤ pkgB2_epsilonBase MS B T J0 gap hT E N := by
  unfold pkgB2_epsilonBase
  exact Finset.sum_nonneg fun i hi =>
    pkgB2_baseCoordinateError_nonneg MS B T J0 gap hT E N i

private theorem pkgB2_baseResidue_uniform {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (hJ0 : ∀ k, 0 < J0 k) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (p : Fin (b * sl) → ℕ)
    (hreg : pkgB2_baseRegular MS B T J0 gap hT N p)
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))))
    (σ : Fin (Fintype.card (pkgB2_Occurrence T E)) → ℕ)
    (hσ : ∀ u, divisorTemplateLaw MS.core.parameters N
      (pkgB2_divisorFamily B U u) (σ u) ≠ 0) :
    finiteL1
      (baseResidueLaw (∏ u, σ u)
        (Finset.prod_pos fun u _ =>
          lt_of_lt_of_le Nat.zero_lt_one
            (pkgB2_divisorFamily_support_specs MS B U u N (σ u) (hσ u)).1)
        (pkgB2_baseMass MS B T J0 gap hT N p))
      (uniformBaseResidueLaw (∏ u, σ u) (Fintype.card (pkgB2_Coord T))) ≤
      pkgB2_epsilonBase MS B T J0 gap hT E N := by
  classical
  let q := Fintype.card (pkgB2_Occurrence T E)
  let Q := ∏ u : Fin q, σ u
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun u _ =>
      lt_of_lt_of_le Nat.zero_lt_one
        (pkgB2_divisorFamily_support_specs MS B U u N (σ u) (hσ u)).1
  have hQcop : Nat.Coprime Q (primorial (N + 1)) := by
    dsimp [Q]
    rw [Nat.coprime_fintype_prod_left_iff]
    intro u
    exact (pkgB2_divisorFamily_support_specs MS B U u N (σ u) (hσ u)).2.2
  have hQle : Q ≤ pkgB2_blockScale MS.core.parameters B N ^
      Fintype.card (pkgB2_Occurrence T E) := by
    dsimp [Q]
    calc
      ∏ u : Fin q, σ u ≤ ∏ _u : Fin q, pkgB2_blockScale MS.core.parameters B N :=
        Finset.prod_le_prod fun u hu =>
          (pkgB2_divisorFamily_support_specs MS B U u N (σ u) (hσ u)).2.1
      _ = pkgB2_blockScale MS.core.parameters B N ^ q := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hδ (i : Fin (Fintype.card (pkgB2_Coord T))) :
      finiteL1
        (pkgB2_coordinateResidueLaw MS B T J0 gap hT N p Q hQpos i)
        (uniformResidueLaw Q) ≤
        pkgB2_baseCoordinateError MS B T J0 gap hT E N i := by
    exact pkgB2_coordinateResidueL1_le_error MS B T J0 gap hgap hJ0 hT N p
      hreg E Q hQpos hQcop hQle i
  have hres := pkgB2_baseResidueL1_le_coordinate_errors MS B T J0 gap hT N p
    hreg Q hQpos (fun i => pkgB2_baseCoordinateError MS B T J0 gap hT E N i) hδ
  simpa [Q, q, pkgB2_epsilonBase] using hres


/-! CRT pushforward and product L1 estimates adapted from the moment package. -/

private noncomputable def pkgB2_CRTPrimeProduct (w V : ℕ) : ℕ :=
  ∏ p : CRTPrimeRange w V, p.val

open scoped Function in
private theorem pkgB2_CRTPrimePairwiseCoprime (w V : ℕ) :
    Pairwise (Nat.Coprime on fun p : CRTPrimeRange w V => p.val) := by
  intro p q hpq
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hq : q.val.Prime := (Finset.mem_filter.mp q.property).2
  have hpne : p.val ≠ q.val := by
    intro h
    apply hpq
    exact Subtype.ext h
  exact (hp.coprime_iff_not_dvd).2 (fun hdiv =>
    hpne ((Nat.prime_dvd_prime_iff_eq hp hq).1 hdiv))

private noncomputable def pkgB2_CRTPrimeRingEquiv (w V : ℕ) :
    ZMod (pkgB2_CRTPrimeProduct w V) ≃+*
      (∀ p : CRTPrimeRange w V, ZMod p.val) := by
  exact ZMod.prodEquivPi (fun p : CRTPrimeRange w V => p.val)
    (pkgB2_CRTPrimePairwiseCoprime w V)

private noncomputable def pkgB2_CRTPrimeUnitsEquiv (w V : ℕ) :
    (ZMod (pkgB2_CRTPrimeProduct w V))ˣ ≃*
      (∀ p : CRTPrimeRange w V, (ZMod p.val)ˣ) :=
  (Units.mapEquiv (pkgB2_CRTPrimeRingEquiv w V).toMulEquiv).trans
    MulEquiv.piUnits

private theorem pkgB2_CRTPrimeProduct_eq_finset (w V : ℕ) :
    pkgB2_CRTPrimeProduct w V =
      ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p := by
  unfold pkgB2_CRTPrimeProduct CRTPrimeRange
  symm
  exact Finset.prod_subtype _ (by intro p; rfl) (fun p => p)

private theorem pkgB2_CRTPrimeProduct_dvd_master (w e V : ℕ) :
    pkgB2_CRTPrimeProduct w V ∣ masterCRTModulus w e V := by
  rw [masterCRTModulus, pkgB2_CRTPrimeProduct_eq_finset]
  exact dvd_mul_of_dvd_right (dvd_refl _) _

private noncomputable def pkgB2_CRTUnitMap (w e V : ℕ) :
    (ZMod (masterCRTModulus w e V))ˣ →*
      (∀ p : CRTPrimeRange w V, (ZMod p.val)ˣ) :=
  (pkgB2_CRTPrimeUnitsEquiv w V).toMonoidHom.comp
    (ZMod.unitsMap (pkgB2_CRTPrimeProduct_dvd_master w e V))

private theorem pkgB2_CRTUnitMap_surjective (w e V : ℕ) :
    Function.Surjective (pkgB2_CRTUnitMap w e V) := by
  let Q := masterCRTModulus w e V
  have hQ : Q ≠ 0 := by
    have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
    change masterCRTModulus w e V ≠ 0
    rw [masterCRTModulus]
    exact (Nat.mul_pos (pow_pos (primorial_pos w) e) hprod).ne'
  letI : NeZero Q := ⟨hQ⟩
  exact (pkgB2_CRTPrimeUnitsEquiv w V).surjective.comp
    (ZMod.unitsMap_surjective (pkgB2_CRTPrimeProduct_dvd_master w e V))

private noncomputable def pkgB2_CRTProjection (w V Q : ℕ) :
    Fin Q → CRTResidues w V := fun a p =>
  ⟨a.val % p.val, Nat.mod_lt _ ((Finset.mem_filter.mp p.property).2.pos)⟩

private noncomputable def pkgB2_FinCoprimeEquivUnits (Q : ℕ) (hQ : 0 < Q) :
    {a : Fin Q // Nat.Coprime a.val Q} ≃ (ZMod Q)ˣ := by
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  refine
    { toFun := fun a => ZMod.unitOfCoprime a.val a.property
      invFun := fun u =>
        ⟨⟨(u : ZMod Q).val, ZMod.val_lt _⟩, ZMod.val_coe_unit_coprime u⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    apply Subtype.ext
    apply Fin.ext
    simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt a.1.isLt]
  · intro u
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

private theorem pkgB2_CRTUnitMap_apply {w e V : ℕ}
    (u : (ZMod (masterCRTModulus w e V))ˣ) (p : CRTPrimeRange w V) :
    (pkgB2_CRTUnitMap w e V u p : ZMod p.val) =
      ((u : ZMod (masterCRTModulus w e V)).cast : ZMod p.val) := by
  let P := ∏ p : CRTPrimeRange w V, p.val
  have hpP : p.val ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
  have hPQ : P ∣ masterCRTModulus w e V := by
    dsimp [P]
    exact pkgB2_CRTPrimeProduct_dvd_master w e V
  have hpQ : p.val ∣ masterCRTModulus w e V := Nat.dvd_trans hpP hPQ
  have hcomp := ZMod.unitsMap_comp hpP hPQ
  have hunit : pkgB2_CRTUnitMap w e V u p = ZMod.unitsMap hpQ u := by
    change ((pkgB2_CRTPrimeUnitsEquiv w V) (ZMod.unitsMap hPQ u)) p = _
    apply Units.ext
    change (ZMod.prodEquivPi (fun p : CRTPrimeRange w V => p.val)
      (pkgB2_CRTPrimePairwiseCoprime w V)
      ((↑(ZMod.unitsMap hPQ u) : ZMod P) :
        ZMod (∏ p : CRTPrimeRange w V, p.val))) p =
        (ZMod.unitsMap hpQ u : ZMod p.val)
    rw [ZMod.prodEquivPi_apply]
    rw [ZMod.unitsMap_val hPQ u, ZMod.unitsMap_val hpQ u]
    change (ZMod.castHom hpP (ZMod p.val))
      ((ZMod.castHom hPQ (ZMod P)) (u : ZMod (masterCRTModulus w e V))) =
      (ZMod.castHom hpQ (ZMod p.val)) (u : ZMod (masterCRTModulus w e V))
    rw [← RingHom.comp_apply, ZMod.castHom_comp]
  rw [hunit, ZMod.unitsMap_val]

private theorem pkgB2_CRTProjection_eq_mappedUnit {w e V : ℕ}
    (hQ : 0 < masterCRTModulus w e V)
    (a : Fin (masterCRTModulus w e V))
    (ha : Nat.Coprime a.val (masterCRTModulus w e V)) (p : CRTPrimeRange w V) :
    (pkgB2_CRTProjection w V (masterCRTModulus w e V) a p).val =
      ((pkgB2_CRTUnitMap w e V
        (pkgB2_FinCoprimeEquivUnits (masterCRTModulus w e V) hQ ⟨a, ha⟩) p :
          ZMod p.val).val) := by
  have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
  letI : NeZero p.val := ⟨hpPrime.ne_zero⟩
  have hpQ : p.val ∣ masterCRTModulus w e V := by
    exact Nat.dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ p))
      (pkgB2_CRTPrimeProduct_dvd_master w e V)
  have haUnit :
      (pkgB2_FinCoprimeEquivUnits (masterCRTModulus w e V) hQ ⟨a, ha⟩ :
        ZMod (masterCRTModulus w e V)) = (a.val : ZMod (masterCRTModulus w e V)) := by
    simp [pkgB2_FinCoprimeEquivUnits, ZMod.coe_unitOfCoprime]
  rw [pkgB2_CRTUnitMap_apply]
  rw [haUnit]
  simp [pkgB2_CRTProjection, pkgB2_FinCoprimeEquivUnits,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast hpQ, ZMod.val_natCast]

private abbrev pkgB2_CRTUnitTuple (w V : ℕ) :=
  ∀ p : CRTPrimeRange w V, (ZMod p.val)ˣ

private noncomputable instance pkgB2_CRTUnitTupleFintype (w V : ℕ) :
    Fintype (pkgB2_CRTUnitTuple w V) := by
  classical
  letI : Fintype (CRTPrimeRange w V) :=
    Finset.Subtype.fintype ((Finset.Ioc w (V + 1)).filter Nat.Prime)
  letI : ∀ p : CRTPrimeRange w V, Fintype (ZMod p.val)ˣ := fun p => Fintype.ofFinite _
  infer_instance

private noncomputable def pkgB2_CRTUniformLaw {w V : ℕ} (r : CRTResidues w V) : ℝ :=
  ∏ p : CRTPrimeRange w V,
    if Nat.Coprime (r p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0

attribute [local instance] Classical.propDecidable in
private theorem pkgB2_CRTUniformLaw_eq_inv_card {w V : ℕ} (r : CRTResidues w V)
    (hr : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val) :
    pkgB2_CRTUniformLaw r = 1 / (Fintype.card (pkgB2_CRTUnitTuple w V) : ℝ) := by
  classical
  letI : Fintype (CRTPrimeRange w V) :=
    Finset.Subtype.fintype ((Finset.Ioc w (V + 1)).filter Nat.Prime)
  letI : ∀ p : CRTPrimeRange w V, Fintype (ZMod p.val)ˣ := fun p => Fintype.ofFinite _
  have hcardN : Fintype.card (pkgB2_CRTUnitTuple w V) =
      ∏ p : CRTPrimeRange w V, (p.val - 1) := by
    change Fintype.card (∀ p : CRTPrimeRange w V, (ZMod p.val)ˣ) = _
    rw [Fintype.card_pi]
    exact Fintype.prod_congr
      (fun p : CRTPrimeRange w V => Fintype.card (ZMod p.val)ˣ)
      (fun p => p.val - 1)
      (fun p => by
        letI : NeZero p.val := ⟨(Finset.mem_filter.mp p.property).2.ne_zero⟩
        rw [ZMod.card_units_eq_totient, Nat.totient_prime
          ((Finset.mem_filter.mp p.property).2)])
  have hcardR : (Fintype.card (pkgB2_CRTUnitTuple w V) : ℝ) =
      ∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardN
  unfold pkgB2_CRTUniformLaw
  simp_rw [if_pos (hr _)]
  calc
    _ = ∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      simp
    _ = (∏ p : CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ))⁻¹ := by
      rw [Finset.prod_inv_distrib]
    _ = 1 / (Fintype.card (pkgB2_CRTUnitTuple w V) : ℝ) := by
      rw [hcardR]
      simp [one_div]

attribute [local instance] Classical.propDecidable in
private theorem pkgB2_uniform_pushforward_finite_group {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H]
    (f : G →* H) (hf : Function.Surjective f) (y : H) :
    ∑ x : G, (1 / (Fintype.card G : ℝ)) * (if f x = y then (1 : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  classical
  let x₀ : G := Classical.choose (hf y)
  have hx₀ : f x₀ = y := Classical.choose_spec (hf y)
  let fiber := {x : G // f x = y}
  let e : fiber ≃ f.ker := {
    toFun := fun x : fiber => (⟨x.1 * x₀⁻¹, by
      change f (x.1 * x₀⁻¹) = 1
      rw [map_mul, map_inv, x.2, hx₀, mul_inv_cancel]⟩ : f.ker)
    invFun := fun k : f.ker => (⟨k.1 * x₀, by
      change f (k.1 * x₀) = y
      rw [map_mul, k.2, one_mul, hx₀]⟩ : fiber)
    left_inv x := by
      apply Subtype.ext
      change (x.1 * x₀⁻¹) * x₀ = x.1
      simp [mul_assoc]
    right_inv k := by
      apply Subtype.ext
      change (k.1 * x₀) * x₀⁻¹ = k.1
      simp [mul_assoc]
  }
  have hfiber :
      ∑ x : G, (if f x = y then (1 : ℝ) else 0) =
        (Fintype.card f.ker : ℝ) := by
    calc
      _ = ((Finset.univ.filter fun x : G => f x = y).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (Fintype.card fiber : ℝ) := by
        exact_mod_cast (Fintype.card_subtype (fun x : G => f x = y)).symm
      _ = (Fintype.card f.ker : ℝ) := by
        exact_mod_cast Fintype.card_congr e
  have hrange : Fintype.card f.range = Fintype.card H := by
    exact Fintype.card_congr (Equiv.ofBijective (fun x : f.range => (x : H))
      ⟨Subtype.val_injective, fun z => ⟨⟨z, hf z⟩, rfl⟩⟩)
  have hcardN : Fintype.card G = Fintype.card f.ker * Fintype.card H := by
    rw [← hrange]
    exact finite_group_kernel_cardinality f
  have hcardR : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * (Fintype.card H : ℝ) := by
    exact_mod_cast hcardN
  calc
    _ = (1 / (Fintype.card G : ℝ)) * (Fintype.card f.ker : ℝ) := by
      rw [← Finset.mul_sum, hfiber]
    _ = 1 / (Fintype.card H : ℝ) := by rw [hcardR]; field_simp

attribute [local instance] Classical.propDecidable in
private theorem pkgB2_CRTUniformProjectionLaw_eq {w e V : ℕ} (r : CRTResidues w V) :
    (∑ a : Fin (masterCRTModulus w e V),
      uniformUnitResidueLaw (masterCRTModulus w e V) a *
        (if pkgB2_CRTProjection w V (masterCRTModulus w e V) a = r then (1 : ℝ) else 0)) =
      pkgB2_CRTUniformLaw r := by
  classical
  let Q := masterCRTModulus w e V
  have hQpos : 0 < Q := by
    have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
    change 0 < masterCRTModulus w e V
    rw [masterCRTModulus]
    exact Nat.mul_pos (pow_pos (primorial_pos w) e) hprod
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  let Source := {a : Fin Q // Nat.Coprime a.val Q}
  let G := (ZMod Q)ˣ
  let c : ℝ := 1 / (Fintype.card G : ℝ)
  let ind : Fin Q → ℝ := fun a =>
    if pkgB2_CRTProjection w V Q a = r then 1 else 0
  let good : Fin Q → Prop := fun a => Nat.Coprime a.val Q
  let eUnit : Source ≃ G := pkgB2_FinCoprimeEquivUnits Q hQpos
  have hcardR : (Fintype.card G : ℝ) = (Nat.totient Q : ℝ) := by
    have hcard : Fintype.card (ZMod Q)ˣ = Nat.totient Q :=
      ZMod.card_units_eq_totient (n := Q)
    exact_mod_cast hcard
  have hsource :
      (∑ a : Fin Q, uniformUnitResidueLaw Q a * ind a) =
        ∑ a : Source, c * ind a.1 := by
    have hterm (a : Fin Q) :
        uniformUnitResidueLaw Q a * ind a =
          if good a then c * ind a else 0 := by
      by_cases ha : Nat.Coprime a.val Q <;>
        by_cases hi : pkgB2_CRTProjection w V Q a = r <;>
        simp [uniformUnitResidueLaw, good, c, ind, ha, hi, hcardR]
    calc
      _ = ∑ a : Fin Q, if good a then c * ind a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a
      _ = (∑ a : Source, (if good a.1 then c * ind a.1 else 0)) +
            ∑ a : {a : Fin Q // ¬ good a}, (if good a.1 then c * ind a.1 else 0) := by
        exact (Fintype.sum_subtype_add_sum_subtype good
          (fun a : Fin Q => if good a then c * ind a else 0)).symm
      _ = ∑ a : Source, c * ind a.1 := by
        have hgoodSum :
            (∑ a : Source, (if good a.1 then c * ind a.1 else 0)) =
              ∑ a : Source, c * ind a.1 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact if_pos a.property
        have hbadSum :
            (∑ a : {a : Fin Q // ¬ good a},
              (if good a.1 then c * ind a.1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          exact if_neg a.property
        rw [hgoodSum, hbadSum]
        simp
  by_cases hgood : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
  · let rUnit : pkgB2_CRTUnitTuple w V := fun p =>
      ZMod.unitOfCoprime (r p).val (hgood p)
    let groupInd : G → ℝ := fun u =>
      @ite ℝ (pkgB2_CRTUnitMap w e V u = rUnit)
        (Classical.propDecidable _) 1 0
    have hiff (a : Source) :
        pkgB2_CRTProjection w V Q a.1 = r ↔
          pkgB2_CRTUnitMap w e V (eUnit a) = rUnit := by
      constructor
      · intro hr
        funext p
        have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
        letI : NeZero p.val := ⟨hpPrime.ne_zero⟩
        apply Units.ext
        apply ZMod.val_injective p.val
        calc
          (pkgB2_CRTUnitMap w e V (eUnit a) p : ZMod p.val).val =
              (pkgB2_CRTProjection w V Q a.1 p).val :=
                (pkgB2_CRTProjection_eq_mappedUnit hQpos a.1 a.2 p).symm
          _ = (r p).val := congrArg Fin.val (congrFun hr p)
          _ = (rUnit p : ZMod p.val).val := by
                simp [rUnit, ZMod.coe_unitOfCoprime, ZMod.val_natCast,
                  Nat.mod_eq_of_lt (r p).isLt]
      · intro hu
        funext p
        have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
        letI : NeZero p.val := ⟨hpPrime.ne_zero⟩
        apply Fin.ext
        have hv := congrArg (fun u : (ZMod p.val)ˣ => (u : ZMod p.val).val)
          (congrFun hu p)
        calc
          (pkgB2_CRTProjection w V Q a.1 p).val =
              (pkgB2_CRTUnitMap w e V (eUnit a) p : ZMod p.val).val :=
                pkgB2_CRTProjection_eq_mappedUnit hQpos a.1 a.2 p
          _ = (r p).val := by
                simpa [rUnit, ZMod.coe_unitOfCoprime, ZMod.val_natCast,
                  Nat.mod_eq_of_lt (r p).isLt] using hv
    have hsumGroup :
        (∑ a : Source, c * ind a.1) =
          ∑ u : G, c * groupInd u := by
      calc
        _ = ∑ a : Source,
              c * groupInd (eUnit a) := by
                apply Finset.sum_congr rfl
                intro a ha
                by_cases h : pkgB2_CRTProjection w V Q a.1 = r
                · simp [ind, groupInd, h, (hiff a).mp h]
                · have hh : pkgB2_CRTUnitMap w e V (eUnit a) ≠ rUnit := by
                    intro hu
                    exact h ((hiff a).mpr hu)
                  simp [ind, groupInd, h, hh]
        _ = ∑ u : G, c * groupInd u :=
              Fintype.sum_equiv eUnit _ _ (fun _ => rfl)
    have hgroup := pkgB2_uniform_pushforward_finite_group
      (pkgB2_CRTUnitMap w e V) (pkgB2_CRTUnitMap_surjective w e V) rUnit
    calc
      _ = ∑ a : Source, c * ind a.1 := hsource
      _ = 1 / (Fintype.card (pkgB2_CRTUnitTuple w V) : ℝ) := by
            rw [hsumGroup]
            dsimp [c, groupInd]
            exact hgroup
      _ = pkgB2_CRTUniformLaw r := (pkgB2_CRTUniformLaw_eq_inv_card r hgood).symm
  · push_neg at hgood
    obtain ⟨p, hpBad⟩ := hgood
    have hzero : (∑ a : Source, c * ind a.1) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases h : pkgB2_CRTProjection w V Q a.1 = r
      · have hu := ZMod.val_coe_unit_coprime (pkgB2_CRTUnitMap w e V (eUnit a) p)
        rw [← pkgB2_CRTProjection_eq_mappedUnit hQpos a.1 a.2 p] at hu
        have hr : Nat.Coprime (r p).val p.val := by
          rw [← congrArg Fin.val (congrFun h p)]
          exact hu
        exact (hpBad hr).elim
      · simp [ind, h]
    have hLawZero : pkgB2_CRTUniformLaw r = 0 := by
      unfold pkgB2_CRTUniformLaw
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simp [hpBad]
    calc
      _ = ∑ a : Source, c * ind a.1 := hsource
      _ = 0 := hzero
      _ = pkgB2_CRTUniformLaw r := hLawZero.symm

private theorem pkgB2_finiteL1_pushforward_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (μ ν : α → ℝ) :
    finiteL1
      (fun b => ∑ a, μ a * if f a = b then (1 : ℝ) else 0)
      (fun b => ∑ a, ν a * if f a = b then (1 : ℝ) else 0) ≤ finiteL1 μ ν := by
  classical
  unfold finiteL1
  have hdiff (b : β) :
      (∑ a, μ a * (if f a = b then (1 : ℝ) else 0)) -
        (∑ a, ν a * (if f a = b then (1 : ℝ) else 0)) =
      ∑ a, (μ a - ν a) * (if f a = b then (1 : ℝ) else 0) := by
    calc
      _ = ∑ a ∈ (Finset.univ : Finset α),
            (μ a * (if f a = b then (1 : ℝ) else 0) -
              ν a * (if f a = b then (1 : ℝ) else 0)) := by
          change
            (∑ a ∈ (Finset.univ : Finset α), μ a *
                (if f a = b then (1 : ℝ) else 0)) -
              ∑ a ∈ (Finset.univ : Finset α), ν a *
                (if f a = b then (1 : ℝ) else 0) = _
          rw [← Finset.sum_sub_distrib]
      _ = ∑ a, (μ a - ν a) * (if f a = b then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
  calc
    _ = ∑ b, |∑ a, (μ a - ν a) * if f a = b then (1 : ℝ) else 0| := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← hdiff b]
    _ ≤ ∑ b, ∑ a, |(μ a - ν a) * if f a = b then (1 : ℝ) else 0| := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |μ a - ν a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ b, if f a = b then |μ a - ν a| else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases h : f a = b <;> simp [h, abs_mul]
        _ = |μ a - ν a| := by simp

private noncomputable def pkgB2_PrimePoolSupport (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter Nat.Prime

private theorem pkgB2_PrimePoolLaw_zero_of_not_mem (lo hi p : ℕ)
    (hp : p ∉ pkgB2_PrimePoolSupport lo hi) : primePoolLaw lo hi p = 0 := by
  have hcond : ¬(lo ≤ p ∧ p < hi ∧ p.Prime) := by
    intro h
    exact hp (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
  simp [primePoolLaw, hcond]

private theorem pkgB2_PrimePoolResidueLaw_eq_sum {lo hi Q : ℕ} (a : Fin Q) :
    primePoolResidueLaw lo hi Q a =
      ∑ p ∈ pkgB2_PrimePoolSupport lo hi,
        primePoolLaw lo hi p * if p % Q = a.val then (1 : ℝ) else 0 := by
  classical
  unfold primePoolResidueLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hpIco : p ∈ Finset.Ico lo hi := (Finset.mem_filter.mp hp).1
  have hcond : lo ≤ p ∧ p < hi ∧ p.Prime :=
    ⟨(Finset.mem_Ico.mp hpIco).1, (Finset.mem_Ico.mp hpIco).2,
      (Finset.mem_filter.mp hp).2⟩
  by_cases hres : p % Q = a.val <;> simp [primePoolLaw, hcond, hres]

private theorem pkgB2_CRTProjection_integerCRTResidues {w e V : ℕ} (n : ℕ) :
    integerCRTResidues w V n =
      pkgB2_CRTProjection w V (masterCRTModulus w e V)
        ⟨n % masterCRTModulus w e V, Nat.mod_lt _ (by
          have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
            Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
          rw [masterCRTModulus]
          exact Nat.mul_pos (pow_pos (primorial_pos w) e) hprod)⟩ := by
  classical
  let Q := masterCRTModulus w e V
  have hQ : 0 < Q := by
    have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
    change 0 < masterCRTModulus w e V
    rw [masterCRTModulus]
    exact Nat.mul_pos (pow_pos (primorial_pos w) e) hprod
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  funext p
  apply Fin.ext
  have hpPrime : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hpQ : p.val ∣ Q := Nat.dvd_trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ p))
    (pkgB2_CRTPrimeProduct_dvd_master w e V)
  simp [integerCRTResidues, pkgB2_CRTProjection, Q, Nat.mod_mod_of_dvd n hpQ]

private theorem pkgB2_PrimePoolCRTProjectionLaw_eq {w e V lo hi : ℕ}
    (r : CRTResidues w V) :
    (∑' n : ℕ, primePoolLaw lo hi n *
      (if integerCRTResidues w V n = r then (1 : ℝ) else 0)) =
      ∑ a : Fin (masterCRTModulus w e V),
        primePoolResidueLaw lo hi (masterCRTModulus w e V) a *
          (if pkgB2_CRTProjection w V (masterCRTModulus w e V) a = r then
            (1 : ℝ) else 0) := by
  classical
  let Q := masterCRTModulus w e V
  let S := pkgB2_PrimePoolSupport lo hi
  have hQpos : 0 < Q := by
    have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
    change 0 < masterCRTModulus w e V
    rw [masterCRTModulus]
    exact Nat.mul_pos (pow_pos (primorial_pos w) e) hprod
  have hzero (n : ℕ) (hn : n ∉ S) :
      primePoolLaw lo hi n *
        (if integerCRTResidues w V n = r then (1 : ℝ) else 0) = 0 := by
    rw [pkgB2_PrimePoolLaw_zero_of_not_mem lo hi n (by simpa [S] using hn)]
    simp
  have hresidue (n : ℕ) :
      ∑ a : Fin Q, (if n % Q = a.val then (1 : ℝ) else 0) *
        (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) =
      (if pkgB2_CRTProjection w V Q
          ⟨n % Q, Nat.mod_lt _ hQpos⟩ = r then (1 : ℝ) else 0) := by
    let a₀ : Fin Q := ⟨n % Q, Nat.mod_lt _ hQpos⟩
    have hcond (a : Fin Q) : n % Q = a.val ↔ a = a₀ := by
      constructor
      · intro h
        apply Fin.ext
        exact h.symm
      · intro h
        simpa [a₀] using congrArg Fin.val h.symm
    calc
      _ = ∑ a : Fin Q,
            if a = a₀ then
              (if pkgB2_CRTProjection w V Q a₀ = r then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases ha₀ : a = a₀
          · subst a
            simp [a₀]
          · have hnot : n % Q ≠ a.val := by
              intro h
              exact ha₀ ((hcond a).mp h)
            simp [ha₀, hnot]
      _ = (if pkgB2_CRTProjection w V Q a₀ = r then (1 : ℝ) else 0) := by
        simp [a₀]
  have hcrt (n : ℕ) :
      integerCRTResidues w V n =
        pkgB2_CRTProjection w V Q ⟨n % Q, Nat.mod_lt _ hQpos⟩ := by
    simpa [Q] using pkgB2_CRTProjection_integerCRTResidues (w := w) (e := e) (V := V) n
  have hproject (n : ℕ) :
      (if integerCRTResidues w V n = r then (1 : ℝ) else 0) =
        ∑ a : Fin Q, (if n % Q = a.val then (1 : ℝ) else 0) *
          (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
    rw [hcrt n]
    exact (hresidue n).symm
  calc
    _ = ∑ n ∈ S, primePoolLaw lo hi n *
          (if integerCRTResidues w V n = r then (1 : ℝ) else 0) := by
        rw [tsum_eq_sum (s := S) hzero]
    _ = ∑ n ∈ S, primePoolLaw lo hi n *
          ∑ a : Fin Q,
            (if n % Q = a.val then (1 : ℝ) else 0) *
              (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hproject n]
    _ = ∑ n ∈ S, ∑ a : Fin Q,
          primePoolLaw lo hi n * (if n % Q = a.val then (1 : ℝ) else 0) *
            (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        calc
          _ = ∑ a : Fin Q,
                primePoolLaw lo hi n *
                  ((if n % Q = a.val then (1 : ℝ) else 0) *
                    (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0)) :=
              Finset.mul_sum (Finset.univ : Finset (Fin Q))
                (fun a => (if n % Q = a.val then (1 : ℝ) else 0) *
                  (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0))
                (primePoolLaw lo hi n)
          _ = ∑ a : Fin Q,
                (primePoolLaw lo hi n * (if n % Q = a.val then (1 : ℝ) else 0)) *
                  (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro a ha
                ring
    _ = ∑ a : Fin Q, ∑ n ∈ S,
          primePoolLaw lo hi n * (if n % Q = a.val then (1 : ℝ) else 0) *
            (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ a : Fin Q,
          primePoolResidueLaw lo hi Q a *
            (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_mul, pkgB2_PrimePoolResidueLaw_eq_sum]

private noncomputable def pkgB2_PrimePoolCRTActualLaw (w V lo hi : ℕ)
    (r : CRTResidues w V) : ℝ :=
  ∑' n : ℕ, primePoolLaw lo hi n *
    (if integerCRTResidues w V n = r then (1 : ℝ) else 0)

private theorem pkgB2_PrimeTupleCRTLaw_eq_prod {m w V : ℕ}
    (lo upper : Fin m → ℕ) (r : Fin m → CRTResidues w V) :
    primeTupleCRTLaw lo upper w V r =
      ∏ i : Fin m, pkgB2_PrimePoolCRTActualLaw w V (lo i) (upper i) (r i) := by
  classical
  let S : Fin m → Finset ℕ := fun i => pkgB2_PrimePoolSupport (lo i) (upper i)
  let T : Finset (Fin m → ℕ) := Fintype.piFinset S
  let f : Fin m → ℕ → ℝ := fun i n => primePoolLaw (lo i) (upper i) n *
    (if integerCRTResidues w V n = r i then (1 : ℝ) else 0)
  have hindicator (p : Fin m → ℕ) :
      (if (fun i => integerCRTResidues w V (p i)) = r then (1 : ℝ) else 0) =
        ∏ i : Fin m, if integerCRTResidues w V (p i) = r i then (1 : ℝ) else 0 := by
    by_cases hEq : (fun i => integerCRTResidues w V (p i)) = r
    · subst r
      simp
    · have hne : ∃ i, integerCRTResidues w V (p i) ≠ r i := by
        by_contra h
        apply hEq
        funext i
        exact not_ne_iff.mp (not_exists.mp h i)
      obtain ⟨i, hrow⟩ := hne
      simp only [if_neg hEq]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hrow])).symm
  have hterm (p : Fin m → ℕ) :
      independentPrimePoolMass lo upper p *
        (if (fun i => integerCRTResidues w V (p i)) = r then (1 : ℝ) else 0) =
      ∏ i : Fin m, f i (p i) := by
    unfold independentPrimePoolMass
    rw [hindicator]
    rw [← Finset.prod_mul_distrib]
  have hzero (p : Fin m → ℕ) (hp : p ∉ T) :
      independentPrimePoolMass lo upper p *
        (if (fun i => integerCRTResidues w V (p i)) = r then (1 : ℝ) else 0) = 0 := by
    rw [hterm p]
    have hnot : ¬∀ i : Fin m, p i ∈ S i := by simpa [T] using hp
    obtain ⟨i, hmem⟩ := not_forall.mp hnot
    have hlaw : primePoolLaw (lo i) (upper i) (p i) = 0 :=
      pkgB2_PrimePoolLaw_zero_of_not_mem (lo i) (upper i) (p i)
        (by simpa [S] using hmem)
    have hfi : f i (p i) = 0 := by simp [f, hlaw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfi
  calc
    _ = ∑ p ∈ T, independentPrimePoolMass lo upper p *
          (if (fun i => integerCRTResidues w V (p i)) = r then (1 : ℝ) else 0) := by
        unfold primeTupleCRTLaw
        rw [tsum_eq_sum (s := T) hzero]
    _ = ∑ p ∈ T, ∏ i : Fin m, f i (p i) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hterm p
    _ = ∏ i : Fin m, ∑ n ∈ S i, f i n := by
        symm
        exact Finset.prod_univ_sum S f
    _ = ∏ i : Fin m, pkgB2_PrimePoolCRTActualLaw w V (lo i) (upper i) (r i) := by
        apply Finset.prod_congr rfl
        intro i himem
        unfold pkgB2_PrimePoolCRTActualLaw
        symm
        apply tsum_eq_sum (s := S i)
        intro n hn
        have hlaw : primePoolLaw (lo i) (upper i) n = 0 :=
          pkgB2_PrimePoolLaw_zero_of_not_mem (lo i) (upper i) n
            (by simpa [S] using hn)
        simp [f, hlaw]

private theorem pkgB2_UniformUnitResidueLaw_sum_eq_one (Q : ℕ) (hQ : 0 < Q) :
    ∑ a : Fin Q, uniformUnitResidueLaw Q a = 1 := by
  classical
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let Source := {a : Fin Q // Nat.Coprime a.val Q}
  let G := (ZMod Q)ˣ
  let c : ℝ := 1 / (Fintype.card G : ℝ)
  let good : Fin Q → Prop := fun a => Nat.Coprime a.val Q
  let eUnit : Source ≃ G := pkgB2_FinCoprimeEquivUnits Q hQ
  have hcardR : (Fintype.card G : ℝ) = (Nat.totient Q : ℝ) := by
    have hcard : Fintype.card (ZMod Q)ˣ = Nat.totient Q :=
      ZMod.card_units_eq_totient (n := Q)
    exact_mod_cast hcard
  have hterm (a : Fin Q) :
      uniformUnitResidueLaw Q a = if good a then c else 0 := by
    by_cases ha : Nat.Coprime a.val Q <;>
      simp [uniformUnitResidueLaw, good, c, ha, hcardR]
  have hsource :
      (∑ a : Fin Q, uniformUnitResidueLaw Q a) = ∑ a : Source, c := by
    calc
      _ = ∑ a : Fin Q, if good a then c else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a
      _ = (∑ a : Source, (if good a.1 then c else 0)) +
            ∑ a : {a : Fin Q // ¬ good a}, (if good a.1 then c else 0) := by
        exact (Fintype.sum_subtype_add_sum_subtype good
          (fun a : Fin Q => if good a then c else 0)).symm
      _ = ∑ a : Source, c := by
        have hgoodSum :
            (∑ a : Source, (if good a.1 then c else 0)) = ∑ a : Source, c := by
          apply Finset.sum_congr rfl
          intro a ha
          exact if_pos a.property
        have hbadSum :
            (∑ a : {a : Fin Q // ¬ good a}, (if good a.1 then c else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          exact if_neg a.property
        rw [hgoodSum, hbadSum]
        simp
  have hcardSource : Fintype.card Source = Fintype.card G :=
    Fintype.card_congr eUnit
  calc
    _ = ∑ a : Source, c := hsource
    _ = (Fintype.card Source : ℝ) * c := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
      rw [hcardSource]
      dsimp [c, G]
      have hcardPos : (0 : ℝ) < (Fintype.card (ZMod Q)ˣ : ℝ) := by positivity
      field_simp

private theorem pkgB2_CRTUniformLaw_sum_eq_one {w e V : ℕ} :
    ∑ r : CRTResidues w V, pkgB2_CRTUniformLaw r = 1 := by
  classical
  let Q := masterCRTModulus w e V
  have hQpos : 0 < Q := by
    have hprod : 0 < ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p :=
      Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
    change 0 < masterCRTModulus w e V
    rw [masterCRTModulus]
    exact Nat.mul_pos (pow_pos (primorial_pos w) e) hprod
  calc
    _ = ∑ r : CRTResidues w V, ∑ a : Fin Q,
          uniformUnitResidueLaw Q a *
            (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact (pkgB2_CRTUniformProjectionLaw_eq (w := w) (e := e) (V := V) r).symm
    _ = ∑ a : Fin Q, uniformUnitResidueLaw Q a := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        change (∑ r ∈ (Finset.univ : Finset (CRTResidues w V)),
            uniformUnitResidueLaw Q a *
              (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0)) = _
        rw [← Finset.mul_sum]
        simp
    _ = 1 := pkgB2_UniformUnitResidueLaw_sum_eq_one Q hQpos

private theorem pkgB2_uniformPrimeTupleCRTLaw_eq_prod {m w V : ℕ}
    (r : Fin m → CRTResidues w V) :
    uniformPrimeTupleCRTLaw w V r = ∏ i, pkgB2_CRTUniformLaw (r i) := by
  rfl

private theorem pkgB2_PrimePoolCRTActualLaw_l1_le {w e V lo hi : ℕ} :
    finiteL1 (pkgB2_PrimePoolCRTActualLaw w V lo hi) (pkgB2_CRTUniformLaw (w := w) (V := V)) ≤
      finiteL1 (primePoolResidueLaw lo hi (masterCRTModulus w e V))
        (uniformUnitResidueLaw (masterCRTModulus w e V)) := by
  classical
  let Q := masterCRTModulus w e V
  have hμ : pkgB2_PrimePoolCRTActualLaw w V lo hi =
      fun r : CRTResidues w V =>
        ∑ a : Fin Q, primePoolResidueLaw lo hi Q a *
          (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
    funext r
    exact pkgB2_PrimePoolCRTProjectionLaw_eq r
  have hν : pkgB2_CRTUniformLaw (w := w) (V := V) =
      fun r : CRTResidues w V =>
        ∑ a : Fin Q, uniformUnitResidueLaw Q a *
          (if pkgB2_CRTProjection w V Q a = r then (1 : ℝ) else 0) := by
    funext r
    exact (pkgB2_CRTUniformProjectionLaw_eq r).symm
  rw [hμ, hν]
  exact pkgB2_finiteL1_pushforward_le (pkgB2_CRTProjection w V Q)
    (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q)

private theorem pkgB2_CRTUniformLaw_nonneg {w V : ℕ} (r : CRTResidues w V) :
    0 ≤ pkgB2_CRTUniformLaw r := by
  classical
  by_cases hgood : ∀ p : CRTPrimeRange w V, Nat.Coprime (r p).val p.val
  · rw [pkgB2_CRTUniformLaw_eq_inv_card r hgood]
    positivity
  · obtain ⟨p, hp⟩ := not_forall.mp hgood
    have hzero : pkgB2_CRTUniformLaw r = 0 := by
      unfold pkgB2_CRTUniformLaw
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simp [hp]
    rw [hzero]

private theorem pkgB2_PrimeTupleCRT_l1_le {m w V : ℕ}
    (lo hi : Fin m → ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hslot : ∀ i, finiteL1
      (pkgB2_PrimePoolCRTActualLaw w V (lo i) (hi i))
      (pkgB2_CRTUniformLaw (w := w) (V := V)) ≤ δ) :
    finiteL1 (primeTupleCRTLaw lo hi w V) (uniformPrimeTupleCRTLaw w V) ≤
      (m : ℝ) * δ * (1 + δ) ^ m := by
  classical
  let μ : Fin m → CRTResidues w V → ℝ := fun i =>
    pkgB2_PrimePoolCRTActualLaw w V (lo i) (hi i)
  let ν : Fin m → CRTResidues w V → ℝ := fun _ => pkgB2_CRTUniformLaw
  have hνmass (i : Fin m) : ∑ r, |ν i r| = 1 := by
    calc
      _ = ∑ r, pkgB2_CRTUniformLaw r := by
        apply Finset.sum_congr rfl
        intro r hr
        exact abs_of_nonneg (pkgB2_CRTUniformLaw_nonneg r)
      _ = 1 := pkgB2_CRTUniformLaw_sum_eq_one (w := w) (e := 1) (V := V)
  have hμmass (i : Fin m) : ∑ r, |μ i r| ≤ 1 + δ := by
    calc
      _ ≤ ∑ r, (|ν i r| + |μ i r - ν i r|) := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          |μ i r| = |(μ i r - ν i r) + ν i r| := by congr 1 <;> ring
          _ ≤ |μ i r - ν i r| + |ν i r| := abs_add_le _ _
          _ = |ν i r| + |μ i r - ν i r| := by ring
      _ = 1 + finiteL1 (μ i) (ν i) := by
        rw [Finset.sum_add_distrib, hνmass i]
        rfl
      _ ≤ 1 + δ := by
        simpa [add_comm] using add_le_add_left (hslot i) 1
  have hmax (i : Fin m) : max (∑ r, |μ i r|) (∑ r, |ν i r|) ≤ 1 + δ := by
    apply max_le
    · exact hμmass i
    · rw [hνmass i]
      linarith
  let F : Fin m → CRTResidues w V → ℝ := μ
  let G : Fin m → CRTResidues w V → ℝ := ν
  have hprod (i : Fin m) :
      ∏ j ∈ (Finset.univ.erase i),
        max (∑ r, |F j r|) (∑ r, |G j r|) ≤ (1 + δ) ^ m := by
    let s := Finset.univ.erase i
    have hlocal : ∀ j ∈ s,
        max (∑ r, |F j r|) (∑ r, |G j r|) ≤ 1 + δ := by
      intro j hj
      exact hmax j
    have hbase : 1 ≤ 1 + δ := by linarith
    calc
      _ ≤ ∏ j ∈ s, (1 + δ) :=
        Finset.prod_le_prod₀ (fun j hj => by positivity) (fun j hj => hlocal j hj)
      _ = (1 + δ) ^ s.card := by simp [s]
      _ ≤ (1 + δ) ^ m := by
        apply pow_le_pow_right₀ hbase
        have hs : s.card ≤ (Finset.univ : Finset (Fin m)).card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        simpa [s] using hs
  have htel := finite_product_l1_telescoping F G
  have hactual :
      (fun r : Fin m → CRTResidues w V => primeTupleCRTLaw lo hi w V r) =
        (fun r => ∏ i, F i (r i)) := by
    funext r
    simpa [F, μ] using pkgB2_PrimeTupleCRTLaw_eq_prod lo hi r
  have huniform :
      (fun r : Fin m → CRTResidues w V => uniformPrimeTupleCRTLaw w V r) =
        (fun r => ∏ i, G i (r i)) := by
    funext r
    simp [G, ν, pkgB2_uniformPrimeTupleCRTLaw_eq_prod]
  change finiteL1
    (fun r : Fin m → CRTResidues w V => primeTupleCRTLaw lo hi w V r)
    (fun r => uniformPrimeTupleCRTLaw w V r) ≤ _
  rw [hactual, huniform]
  calc
    _ ≤ ∑ i, finiteL1 (F i) (G i) *
        ∏ j ∈ (Finset.univ.erase i), max (∑ r, |F j r|) (∑ r, |G j r|) := htel
    _ ≤ ∑ i, δ * (1 + δ) ^ m := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ δ * ∏ j ∈ (Finset.univ.erase i),
                max (∑ r, |F j r|) (∑ r, |G j r|) :=
                  mul_le_mul_of_nonneg_right (hslot i)
                    (Finset.prod_nonneg fun j hj => by positivity)
          _ ≤ δ * (1 + δ) ^ m := mul_le_mul_of_nonneg_left (hprod i) hδ
    _ = (m : ℝ) * δ * (1 + δ) ^ m := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring

private noncomputable def pkgB2_modulusResidueProject {Qsmall Qbig : ℕ}
    (hsmall : 0 < Qsmall) : Fin Qbig → Fin Qsmall := fun a =>
  ⟨a.val % Qsmall, Nat.mod_lt _ hsmall⟩

private theorem pkgB2_primePoolResidueLaw_projection {lo hi Qsmall Qbig : ℕ}
    (hdiv : Qsmall ∣ Qbig) (hsmall : 0 < Qsmall) (hbig : 0 < Qbig)
    (a : Fin Qsmall) :
    (∑ x : Fin Qbig, primePoolResidueLaw lo hi Qbig x *
      (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0)) =
      primePoolResidueLaw lo hi Qsmall a := by
  classical
  let S : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  let mass := primePoolMass lo hi
  have hnum :
      (∑ x : Fin Qbig,
        (∑ p ∈ S, if p % Qbig = x.val then 1 / (p : ℝ) else 0) *
          (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0)) =
      ∑ p ∈ S, if p % Qsmall = a.val then 1 / (p : ℝ) else 0 := by
    calc
      _ = ∑ p ∈ S, ∑ x : Fin Qbig,
            (if p % Qbig = x.val then 1 / (p : ℝ) else 0) *
              (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_mul]
      _ = ∑ p ∈ S, if p % Qsmall = a.val then 1 / (p : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hpa : p % Qsmall = a.val
        · let x0 : Fin Qbig := ⟨p % Qbig, Nat.mod_lt _ hbig⟩
          have hx0 : x0.val % Qsmall = a.val := by
            change (p % Qbig) % Qsmall = a.val
            rw [Nat.mod_mod_of_dvd p hdiv]
            exact hpa
          have hunique (x : Fin Qbig) : p % Qbig = x.val ↔
              x = x0 := by
            constructor
            · intro hx
              apply Fin.ext
              exact hx.symm
            · intro hx
              simpa [x0] using congrArg Fin.val hx.symm
          calc
            _ = ∑ x : Fin Qbig,
                  if x = x0 then 1 / (p : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro x hx
                by_cases hxp : p % Qbig = x.val
                · have hx' := (hunique x).mp hxp
                  have hproj0 : pkgB2_modulusResidueProject hsmall x0 = a := by
                    apply Fin.ext
                    exact hx0
                  have hproj : pkgB2_modulusResidueProject hsmall x = a := by
                    rw [hx']
                    exact hproj0
                  simp only [if_pos hxp, if_pos hproj, if_pos hx', one_mul, mul_one]
                · have hx' : x ≠ x0 := by
                    intro heq
                    exact hxp ((hunique x).mpr heq)
                  simp [hxp, hx']
            _ = (if p % Qsmall = a.val then 1 / (p : ℝ) else 0) := by simp [hpa]
        · have hterm (x : Fin Qbig) :
              (if p % Qbig = x.val then 1 / (p : ℝ) else 0) *
                (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0) = 0 := by
            by_cases hxp : p % Qbig = x.val
            · have hcompat : x.val % Qsmall = p % Qsmall := by
                calc
                  x.val % Qsmall = (p % Qbig) % Qsmall := by
                    exact congrArg (fun n : ℕ => n % Qsmall) hxp.symm
                  _ = p % Qsmall := Nat.mod_mod_of_dvd p hdiv
              have hbad : x.val % Qsmall ≠ a.val := by
                intro heq
                exact hpa (hcompat.symm.trans heq)
              have hbadFin : pkgB2_modulusResidueProject hsmall x ≠ a := by
                intro heq
                exact hbad (congrArg Fin.val heq)
              simp [hxp, hbadFin]
            · simp [pkgB2_modulusResidueProject, hxp]
          calc
            _ = ∑ x : Fin Qbig, (0 : ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hterm x
            _ = 0 := by simp
            _ = (if p % Qsmall = a.val then 1 / (p : ℝ) else 0) := by simp [hpa]
  unfold primePoolResidueLaw
  dsimp [S, mass] at hnum ⊢
  calc
    _ = ∑ x : Fin Qbig,
          ((∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
            if p % Qbig = x.val then 1 / (p : ℝ) else 0) *
            (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0)) /
          primePoolMass lo hi := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (∑ x : Fin Qbig,
          (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
            if p % Qbig = x.val then 1 / (p : ℝ) else 0) *
            (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0)) /
          primePoolMass lo hi := by rw [Finset.sum_div]
    _ = (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
          if p % Qsmall = a.val then 1 / (p : ℝ) else 0) /
          primePoolMass lo hi := by rw [hnum]
    _ = primePoolResidueLaw lo hi Qsmall a := rfl

private theorem pkgB2_uniformUnitResidueLaw_projection {Qsmall Qbig : ℕ}
    (hdiv : Qsmall ∣ Qbig) (hsmall : 0 < Qsmall) (hbig : 0 < Qbig)
    (a : Fin Qsmall) :
    (∑ x : Fin Qbig, uniformUnitResidueLaw Qbig x *
      (if pkgB2_modulusResidueProject hsmall x = a then (1 : ℝ) else 0)) =
      uniformUnitResidueLaw Qsmall a := by
  classical
  letI : NeZero Qbig := ⟨Nat.ne_of_gt hbig⟩
  letI : NeZero Qsmall := ⟨Nat.ne_of_gt hsmall⟩
  let Source := {x : Fin Qbig // Nat.Coprime x.val Qbig}
  let G := (ZMod Qbig)ˣ
  let H := (ZMod Qsmall)ˣ
  let c : ℝ := 1 / (Fintype.card G : ℝ)
  let good : Fin Qbig → Prop := fun x => Nat.Coprime x.val Qbig
  let ind : Fin Qbig → ℝ := fun x =>
    if pkgB2_modulusResidueProject hsmall x = a then 1 else 0
  let eBig : Source ≃ G := pkgB2_FinCoprimeEquivUnits Qbig hbig
  let eSmall : {x : Fin Qsmall // Nat.Coprime x.val Qsmall} ≃ H :=
    pkgB2_FinCoprimeEquivUnits Qsmall hsmall
  let f : G →* H := ZMod.unitsMap hdiv
  have hcardBig : (Fintype.card G : ℝ) = (Nat.totient Qbig : ℝ) := by
    have hcard : Fintype.card (ZMod Qbig)ˣ = Nat.totient Qbig :=
      ZMod.card_units_eq_totient (n := Qbig)
    exact_mod_cast hcard
  have hcardSmall : (Fintype.card H : ℝ) = (Nat.totient Qsmall : ℝ) := by
    have hcard : Fintype.card (ZMod Qsmall)ˣ = Nat.totient Qsmall :=
      ZMod.card_units_eq_totient (n := Qsmall)
    exact_mod_cast hcard
  have hsource :
      (∑ x : Fin Qbig, uniformUnitResidueLaw Qbig x * ind x) =
        ∑ x : Source, c * ind x.1 := by
    have hterm (x : Fin Qbig) :
        uniformUnitResidueLaw Qbig x * ind x =
          if good x then c * ind x else 0 := by
      by_cases hx : Nat.Coprime x.val Qbig <;>
        by_cases hi : pkgB2_modulusResidueProject hsmall x = a <;>
        simp [uniformUnitResidueLaw, good, c, ind, hx, hi, hcardBig]
    calc
      _ = ∑ x : Fin Qbig, if good x then c * ind x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
      _ = (∑ x : Source, (if good x.1 then c * ind x.1 else 0)) +
            ∑ x : {x : Fin Qbig // ¬ good x}, (if good x.1 then c * ind x.1 else 0) := by
        exact (Fintype.sum_subtype_add_sum_subtype good
          (fun x : Fin Qbig => if good x then c * ind x else 0)).symm
      _ = ∑ x : Source, c * ind x.1 := by
        have hgoodSum :
            (∑ x : Source, (if good x.1 then c * ind x.1 else 0)) =
              ∑ x : Source, c * ind x.1 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact if_pos x.property
        have hbadSum :
            (∑ x : {x : Fin Qbig // ¬ good x},
              (if good x.1 then c * ind x.1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          exact if_neg x.property
        rw [hgoodSum, hbadSum, add_zero]
  have hmapval (x : Source) :
      (f (eBig x) : ZMod Qsmall) =
        ((x.1.val % Qsmall : ℕ) : ZMod Qsmall) := by
    rw [ZMod.unitsMap_val hdiv]
    have hx : (eBig x : ZMod Qbig) = (x.1.val : ZMod Qbig) := by
      simp [eBig, pkgB2_FinCoprimeEquivUnits, ZMod.coe_unitOfCoprime]
    rw [hx]
    rw [ZMod.cast_natCast hdiv]
    simp [pkgB2_modulusResidueProject]
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hdiv
  by_cases ha : Nat.Coprime a.val Qsmall
  · let aUnit : H := eSmall ⟨a, ha⟩
    have haUnitVal : (aUnit : ZMod Qsmall) = (a.val : ZMod Qsmall) := by
      simp [aUnit, eSmall, pkgB2_FinCoprimeEquivUnits, ZMod.coe_unitOfCoprime]
    have hcond (x : Source) :
        (pkgB2_modulusResidueProject hsmall x.1 = a) ↔ f (eBig x) = aUnit := by
      constructor
      · intro hx
        apply Units.ext
        rw [hmapval x, haUnitVal]
        exact congrArg (fun n : ℕ => (n : ZMod Qsmall)) (congrArg Fin.val hx)
      · intro hx
        have hval := congrArg (fun u : H => (u : ZMod Qsmall)) hx
        rw [hmapval x, haUnitVal] at hval
        have hnat := congrArg ZMod.val hval
        apply Fin.ext
        simpa [pkgB2_modulusResidueProject,
          Nat.mod_eq_of_lt (Nat.mod_lt _ hsmall), Nat.mod_eq_of_lt a.isLt] using hnat
    have hsumGroup :
        (∑ x : Source, c * ind x.1) =
          ∑ u : G, c * (if f u = aUnit then (1 : ℝ) else 0) := by
      apply Fintype.sum_equiv eBig
      intro x
      simp [ind, hcond x]
    have hgroup := pkgB2_uniform_pushforward_finite_group f hsurj aUnit
    calc
      _ = ∑ x : Source, c * ind x.1 := hsource
      _ = 1 / (Fintype.card H : ℝ) := by
        rw [hsumGroup]
        simpa [c] using hgroup
      _ = uniformUnitResidueLaw Qsmall a := by
        simp [uniformUnitResidueLaw, ha, hcardSmall]
  · have hzero (x : Source) : ind x.1 = 0 := by
      by_contra hne
      have hx : pkgB2_modulusResidueProject hsmall x.1 = a := by
        dsimp [ind] at hne
        split_ifs at hne with h
        · exact h
        · simp at hne
      have hu := ZMod.val_coe_unit_coprime (f (eBig x))
      rw [hmapval x] at hu
      have hu' : Nat.Coprime (x.1.val % Qsmall) Qsmall := by
        simpa [Nat.mod_eq_of_lt (Nat.mod_lt _ hsmall)] using hu
      have hproj : x.1.val % Qsmall = a.val := by
        simpa [pkgB2_modulusResidueProject] using congrArg Fin.val hx
      rw [hproj] at hu'
      exact ha hu'
    calc
      _ = ∑ x : Source, c * ind x.1 := hsource
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hzero x, mul_zero]
      _ = uniformUnitResidueLaw Qsmall a := by
        simp [uniformUnitResidueLaw, ha]

private theorem pkgB2_masterCRTModulus_pos (w e V : ℕ) :
    0 < masterCRTModulus w e V := by
  unfold masterCRTModulus
  apply Nat.mul_pos (pow_pos (primorial_pos w) e)
  apply Finset.prod_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2.pos

private theorem pkgB2_masterCRTModulus_mono_dvd {w e Vsmall Vbig : ℕ}
    (hV : Vsmall ≤ Vbig) :
    masterCRTModulus w e Vsmall ∣ masterCRTModulus w e Vbig := by
  unfold masterCRTModulus
  apply Nat.mul_dvd_mul_left
  apply Finset.prod_dvd_prod_of_subset
    ((Finset.Ioc w (Vsmall + 1)).filter Nat.Prime)
    ((Finset.Ioc w (Vbig + 1)).filter Nat.Prime) (fun p => p)
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIoc, hpPrime⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ?_, hpPrime⟩
  rcases Finset.mem_Ioc.mp hpIoc with ⟨hw, hupper⟩
  exact ⟨hw, le_trans hupper (Nat.add_le_add_right hV 1)⟩

private noncomputable def pkgB2_poolCRTResidueError {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) : ℝ :=
  finiteL1
    (primePoolResidueLaw (MS.primeStage.pool N l).lower (MS.primeStage.pool N l).upper
      (masterCRTModulus (N + 1) (MS.primeStage.e0 N)
        (masterScaleV MS.core.parameters N l)))
    (uniformUnitResidueLaw
      (masterCRTModulus (N + 1) (MS.primeStage.e0 N)
        (masterScaleV MS.core.parameters N l)))

private theorem pkgB2_modulusResidueLaw_l1_mono {lo hi Qsmall Qbig : ℕ}
    (hdiv : Qsmall ∣ Qbig) (hsmall : 0 < Qsmall)
    (hbig : 0 < Qbig) :
    finiteL1 (primePoolResidueLaw lo hi Qsmall) (uniformUnitResidueLaw Qsmall) ≤
      finiteL1 (primePoolResidueLaw lo hi Qbig) (uniformUnitResidueLaw Qbig) := by
  let f : Fin Qbig → Fin Qsmall := pkgB2_modulusResidueProject hsmall
  have hμ : (fun a : Fin Qsmall =>
      ∑ x : Fin Qbig, primePoolResidueLaw lo hi Qbig x *
        (if f x = a then (1 : ℝ) else 0)) = primePoolResidueLaw lo hi Qsmall := by
    funext a
    exact pkgB2_primePoolResidueLaw_projection hdiv hsmall hbig a
  have hν : (fun a : Fin Qsmall =>
      ∑ x : Fin Qbig, uniformUnitResidueLaw Qbig x *
        (if f x = a then (1 : ℝ) else 0)) = uniformUnitResidueLaw Qsmall := by
    funext a
    exact pkgB2_uniformUnitResidueLaw_projection hdiv hsmall hbig a
  rw [← hμ, ← hν]
  exact pkgB2_finiteL1_pushforward_le f
    (primePoolResidueLaw lo hi Qbig) (uniformUnitResidueLaw Qbig)

private theorem pkgB2_PrimePoolCRTActualLaw_l1_le_gap {w e Vsmall Vbig lo hi : ℕ}
    (hV : Vsmall ≤ Vbig) :
    finiteL1
      (pkgB2_PrimePoolCRTActualLaw w Vsmall lo hi)
      (pkgB2_CRTUniformLaw (w := w) (V := Vsmall)) ≤
    finiteL1
      (primePoolResidueLaw lo hi (masterCRTModulus w e Vbig))
      (uniformUnitResidueLaw (masterCRTModulus w e Vbig)) := by
  let Qsmall := masterCRTModulus w e Vsmall
  let Qbig := masterCRTModulus w e Vbig
  have hsmall : 0 < Qsmall := pkgB2_masterCRTModulus_pos w e Vsmall
  have hbig : 0 < Qbig := pkgB2_masterCRTModulus_pos w e Vbig
  have hdiv : Qsmall ∣ Qbig := pkgB2_masterCRTModulus_mono_dvd hV
  calc
    _ ≤ finiteL1 (primePoolResidueLaw lo hi Qsmall) (uniformUnitResidueLaw Qsmall) :=
      pkgB2_PrimePoolCRTActualLaw_l1_le (w := w) (e := e) (V := Vsmall)
    _ ≤ finiteL1 (primePoolResidueLaw lo hi Qbig) (uniformUnitResidueLaw Qbig) :=
      pkgB2_modulusResidueLaw_l1_mono hdiv hsmall hbig

private noncomputable def pkgB2_CRTErrorDelta {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (gap : Fin b → Fin K) (N : ℕ) : ℝ :=
  ∑ i : Fin (b * sl),
    pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i) N

private noncomputable def pkgB2_epsilonCRT {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (gap : Fin b → Fin K) (N : ℕ) : ℝ :=
  (b * sl : ℝ) * pkgB2_CRTErrorDelta MS gap N *
    (1 + pkgB2_CRTErrorDelta MS gap N) ^ (b * sl)

private theorem pkgB2_poolCRTResidueError_nonneg {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (l : Fin K) (N : ℕ) : 0 ≤ pkgB2_poolCRTResidueError MS l N := by
  dsimp [pkgB2_poolCRTResidueError, finiteL1]
  positivity

private theorem pkgB2_CRTErrorDelta_nonneg {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (gap : Fin b → Fin K) (N : ℕ) : 0 ≤ pkgB2_CRTErrorDelta MS gap N := by
  unfold pkgB2_CRTErrorDelta
  exact Finset.sum_nonneg fun i hi =>
    pkgB2_poolCRTResidueError_nonneg MS (pkgB2_repGap gap i) N

private theorem pkgB2_CRTError_bound {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k))
    (N : ℕ) :
    finiteL1
      (primeTupleCRTLaw (m := b * sl)
        (fun i : Fin (b * sl) => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i : Fin (b * sl) => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (N + 1) (pkgB2_blockScale MS.core.parameters B N))
      (uniformPrimeTupleCRTLaw (m := b * sl) (N + 1)
        (pkgB2_blockScale MS.core.parameters B N)) ≤
      pkgB2_epsilonCRT MS gap N := by
  classical
  let m := b * sl
  let V := pkgB2_blockScale MS.core.parameters B N
  let lo : Fin m → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin m → ℕ := fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let δ := pkgB2_CRTErrorDelta MS gap N
  have hδ : 0 ≤ δ := pkgB2_CRTErrorDelta_nonneg MS gap N
  have hVle (i : Fin m) : V ≤ masterScaleV MS.core.parameters N (pkgB2_repGap gap i) := by
    let e := finProdFinEquiv (m := b) (n := sl)
    have hiGap := hgap (e.symm i).1
    simpa [V, pkgB2_repGap, e] using
      pkgB2_blockScale_le_masterScaleV MS.core.parameters B (gap (e.symm i).1)
        hiGap.1 N
  have hslot (i : Fin m) :
      finiteL1
        (pkgB2_PrimePoolCRTActualLaw (N + 1) V (lo i) (hi i))
        (pkgB2_CRTUniformLaw (w := N + 1) (V := V)) ≤ δ := by
    have hactual := pkgB2_PrimePoolCRTActualLaw_l1_le_gap
      (w := N + 1) (e := MS.primeStage.e0 N) (Vsmall := V)
      (Vbig := masterScaleV MS.core.parameters N (pkgB2_repGap gap i))
      (lo := lo i) (hi := hi i) (hVle i)
    have hsum : pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i) N ≤ δ := by
      dsimp [δ, pkgB2_CRTErrorDelta]
      exact Finset.single_le_sum
        (fun j hj => pkgB2_poolCRTResidueError_nonneg MS (pkgB2_repGap gap j) N)
        (Finset.mem_univ i)
    simpa [pkgB2_poolCRTResidueError, lo, hi, V] using hactual.trans hsum
  have htuple := pkgB2_PrimeTupleCRT_l1_le lo hi δ hδ hslot
  simpa [m, V, lo, hi, δ, pkgB2_epsilonCRT, pkgB2_CRTErrorDelta] using htuple

private theorem pkgB2_poolCRTResidueError_superPolynomial {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (l : Fin K) :
    SuperPolynomialSmall (pkgB2_poolCRTResidueError MS l)
      (fun N => (masterScaleV MS.core.parameters N l : ℝ)) := by
  change SuperPolynomialSmall
    (fun N => finiteL1
      (primePoolResidueLaw (MS.primeStage.pool N l).lower (MS.primeStage.pool N l).upper
        (masterCRTModulus (N + 1) (MS.primeStage.e0 N)
          (masterScaleV MS.core.parameters N l)))
      (uniformUnitResidueLaw
        (masterCRTModulus (N + 1) (MS.primeStage.e0 N)
          (masterScaleV MS.core.parameters N l))))
    (fun N => (masterScaleV MS.core.parameters N l : ℝ))
  exact MS.primeStage.pool_residue_error l

private theorem pkgB2_CRTErrorDelta_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k)) :
    SuperPolynomialSmall (pkgB2_CRTErrorDelta MS gap)
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  classical
  let V : ℕ → ℝ := fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)
  let e := finProdFinEquiv (m := b) (n := sl)
  have hvalid (i : Fin (b * sl)) : ValidGap B (pkgB2_repGap gap i) := by
    dsimp [pkgB2_repGap, e]
    exact hgap (e.symm i).1
  have hterm (i : Fin (b * sl)) :
      SuperPolynomialSmall (pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i)) V := by
    let l := pkgB2_repGap gap i
    have hsmall : SuperPolynomialSmall (pkgB2_poolCRTResidueError MS l)
        (fun N => (masterScaleV MS.core.parameters N l : ℝ)) :=
      pkgB2_poolCRTResidueError_superPolynomial MS l
    have hVleS (N : ℕ) : V N ≤ (masterScaleV MS.core.parameters N l : ℝ) := by
      change (pkgB2_blockScale MS.core.parameters B N : ℝ) ≤ _
      exact_mod_cast pkgB2_blockScale_le_masterScaleV MS.core.parameters B l
        (hvalid i).1 N
    apply pkgB2_superPolynomialSmall_scale_transfer hVleS
      (fun _ => by positivity)
      (fun N => pkgB2_poolCRTResidueError_nonneg MS l N) hsmall
  intro C hC
  have htermLimit (i : Fin (b * sl)) :
      Tendsto (fun N => pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i) N * V N ^ C)
        atTop (𝓝 0) := hterm i C hC
  have hsum : Tendsto
      (fun N => ∑ i : Fin (b * sl),
        pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i) N * V N ^ C)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin (b * sl)))
      (fun i hi => htermLimit i)
  have hEq (N : ℕ) :
      pkgB2_CRTErrorDelta MS gap N * V N ^ C =
        ∑ i : Fin (b * sl),
          pkgB2_poolCRTResidueError MS (pkgB2_repGap gap i) N * V N ^ C := by
    simp [pkgB2_CRTErrorDelta, V, Finset.sum_mul]
  apply hsum.congr'
  filter_upwards with N
  exact (hEq N).symm

private theorem pkgB2_tupleCRTErr_superPolynomial {m : ℕ}
    (δ V : ℕ → ℝ) (hδ : SuperPolynomialSmall δ V)
    (hδnonneg : ∀ N, 0 ≤ δ N) (hVone : ∀ N, 1 ≤ V N) :
    SuperPolynomialSmall
      (fun N => (m : ℝ) * δ N * (1 + δ N) ^ m) V := by
  have hδV : Tendsto (fun N => δ N * V N) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hδ 1 (by norm_num)
  have hδle : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 := by
    filter_upwards [hδV.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with N hN
    have hmul : δ N ≤ δ N * V N := by
      calc
        δ N = δ N * 1 := by ring
        _ ≤ δ N * V N := mul_le_mul_of_nonneg_left (hVone N) (hδnonneg N)
    exact le_of_lt (lt_of_le_of_lt hmul hN)
  intro C hC
  have hδC := hδ C hC
  have hsmall : Tendsto
      (fun N => (m : ℝ) * 2 ^ m * (δ N * V N ^ C)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (m : ℝ) * 2 ^ m) atTop
        (𝓝 ((m : ℝ) * 2 ^ m)) := tendsto_const_nhds
    simpa [mul_assoc] using hconst.mul hδC
  have hbound (N : ℕ) (hN : δ N ≤ 1) :
      ((m : ℝ) * δ N * (1 + δ N) ^ m) * V N ^ C ≤
        (m : ℝ) * 2 ^ m * (δ N * V N ^ C) := by
    have hpow : (1 + δ N) ^ m ≤ (2 : ℝ) ^ m := by
      exact pow_le_pow_left₀ (by linarith [hδnonneg N]) (by linarith) m
    have hVnonneg : 0 ≤ V N := by linarith [hVone N]
    have hbase : 0 ≤ (m : ℝ) * δ N * V N ^ C :=
      mul_nonneg (mul_nonneg (by positivity) (hδnonneg N))
        (Real.rpow_nonneg hVnonneg C)
    calc
      _ = ((m : ℝ) * δ N * V N ^ C) * (1 + δ N) ^ m := by ring
      _ ≤ ((m : ℝ) * δ N * V N ^ C) * (2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left hpow hbase
      _ = (m : ℝ) * 2 ^ m * (δ N * V N ^ C) := by ring
  have hupper : ∀ᶠ N : ℕ in atTop,
      ((m : ℝ) * δ N * (1 + δ N) ^ m) * V N ^ C ≤
        (m : ℝ) * 2 ^ m * (δ N * V N ^ C) := by
    filter_upwards [hδle] with N hN
    exact hbound N hN
  have hnonneg (N : ℕ) :
      0 ≤ ((m : ℝ) * δ N * (1 + δ N) ^ m) * V N ^ C := by
    have hVnonneg : 0 ≤ V N := by linarith [hVone N]
    have hδbase : 0 ≤ 1 + δ N := by linarith [hδnonneg N]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (hδnonneg N)) (pow_nonneg hδbase _))
      (Real.rpow_nonneg hVnonneg C)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper hsmall

private theorem pkgB2_epsilonCRT_superPolynomial {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (gap : Fin b → Fin K) (hgap : ∀ k, ValidGap B (gap k)) :
    SuperPolynomialSmall (pkgB2_epsilonCRT MS gap)
      (fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)) := by
  let V : ℕ → ℝ := fun N => (pkgB2_blockScale MS.core.parameters B N : ℝ)
  have hVone (N : ℕ) : 1 ≤ V N := by
    change (1 : ℝ) ≤ (pkgB2_blockScale MS.core.parameters B N : ℝ)
    exact_mod_cast (show 1 ≤ pkgB2_blockScale MS.core.parameters B N by
      dsimp [pkgB2_blockScale]; omega)
  have hδnonneg (N : ℕ) : 0 ≤ pkgB2_CRTErrorDelta MS gap N :=
    pkgB2_CRTErrorDelta_nonneg MS gap N
  have hδ := pkgB2_CRTErrorDelta_superPolynomial MS B gap hgap
  have htuple := pkgB2_tupleCRTErr_superPolynomial (m := b * sl)
    (pkgB2_CRTErrorDelta MS gap) V hδ hδnonneg hVone
  change SuperPolynomialSmall
    (fun N => (b : ℝ) * (sl : ℝ) * pkgB2_CRTErrorDelta MS gap N *
      (1 + pkgB2_CRTErrorDelta MS gap N) ^ (b * sl)) V
  simpa [Nat.cast_mul] using htuple

private theorem pkgB2_modulusResidue_ne_zero {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (k : Fin b)
    (r : ℕ) (hr : r.Prime) (hrN : N + 1 < r)
    (hno : ∀ Q ∈ pkgB2_repTests hT,
      ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) :
    rationalResidue r hr
      ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℚ) ≠ 0 := by
  have hM : ¬ r ∣ MS.core.parameters.M N := by
    obtain ⟨e, he⟩ := MS.core.modulus_power N
    intro hdiv
    rw [he] at hdiv
    have hW : r ∣ primorial (N + 1) := hr.dvd_of_dvd_pow hdiv
    have hle := (Nat.Prime.dvd_primorial_iff hr).mp hW
    omega
  have hD : MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D ∈
      pkgB2_repTests hT := pkgB2_templateModulus_mem hT k
  have hnoD : ¬ ((r : ℤ) ∣ evalIntegerPolynomial (T k).D
      (fun j => (pkgB2_repPrimeProject hT p k j : ℤ))) := by
    intro hdiv
    apply hno (MvPolynomial.rename (pkgB2_templateEmbedding hT k) (T k).D) hD
    rw [pkgB2_renameEval]
    exact hdiv
  have hrough : ¬ r ∣ roughPart (N + 1)
      (evalIntegerPolynomial (T k).D
        (fun j => (pkgB2_repPrimeProject hT p k j : ℤ))) := by
    intro hdiv
    have hnat := pkgB2_prime_dvd_roughPart_implies_dvd_natAbs hr hdiv
    exact hnoD (Int.natCast_dvd.mpr hnat)
  have hmod : ¬ r ∣ (T k).modulus (corrScales MS) N
      (pkgB2_repPrimeProject hT p k) := by
    change ¬ r ∣ MS.core.parameters.M N * roughPart (N + 1)
      (evalIntegerPolynomial (T k).D
        (fun j => (pkgB2_repPrimeProject hT p k j : ℤ)))
    intro hdiv
    rcases hr.dvd_mul.mp hdiv with hMdiv | hroughdiv
    · exact hM hMdiv
    · exact hrough hroughdiv
  have hcast :
      (((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℕ) : ZMod r) ≠ 0 := by
    intro hz
    have hdiv : r ∣ (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact hmod hdiv
  have hres : rationalResidue r hr
      ((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℚ) =
      (((T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k) : ℕ) : ZMod r) := by
    letI : Fact r.Prime := ⟨hr⟩
    simp [rationalResidue]
  rw [hres]
  exact hcast

private theorem pkgB2_pairwiseRowTests {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k))
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (hN0 : pkgB2_directionConstantBound T direction + 1 ≤ N)
    (r : ℕ) (hr : r.Prime) (hrN : N + 1 < r)
    (hno : ∀ Q ∈ pkgB2_repTests hT,
      ¬ ((r : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ))))
    (u v : Fin (Fintype.card (pkgB2_Occurrence T E))) (huv : u ≠ v) :
    ∃ i j, rationalResidue r hr
        (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u i) *
          rationalResidue r hr
            (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p v j) ≠
        rationalResidue r hr
            (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j) *
          rationalResidue r hr
            (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p v i) := by
  classical
  let Mnat : Fin b → ℕ := fun k =>
    (T k).modulus (corrScales MS) N (pkgB2_repPrimeProject hT p k)
  let Mint : Fin b → ℤ := fun k => (Mnat k : ℤ)
  letI : Fact r.Prime := ⟨hr⟩
  have hMcast (k : Fin b) : (Mint k : ZMod r) ≠ 0 := by
    have hrat := pkgB2_modulusResidue_ne_zero MS T hT N p k r hr hrN hno
    have hcast : rationalResidue r hr (Mnat k : ℚ) = (Mnat k : ZMod r) := by
      simp [rationalResidue]
    have hrat' : rationalResidue r hr (Mnat k : ℚ) ≠ 0 := by
      simpa [Mnat] using hrat
    rw [hcast] at hrat'
    simpa [Mint] using hrat'
  have hdirMod (s : pkgB2_Nonroot T) :
      (direction s 0 : ZMod r) ≠ 0 ∧
        ∀ ω' : Finset (Fin (T s.1).d), ω' ≠ s.2.1 →
          (direction s 0 : ZMod r) +
            ∑ j ∈ ω', (direction s j.succ : ZMod r) ≠ 0 :=
    pkgB2_directionSpec_modulo T direction hdir N r hN0 hrN s
  let c : pkgB2_BaseRow T → pkgB2_OldCoord T → ZMod r := fun t j =>
    pkgB2_oldCoefficientField (F := ZMod r) T Mint t j
  let ρ : pkgB2_BaseRow T → pkgB2_Nonroot T → ZMod r := fun t s =>
    ((pkgB2_response T Mint s
      (pkgB2_directionLift (T s.1).d (direction s)) t : ℤ) : ZMod r)
  have ha : ∀ t, c t (.inl ()) = 1 := by
    intro t
    change ((pkgB2_oldCoefficient T Mint t (.inl ()) : ℤ) : ZMod r) = 1
    rw [pkgB2_oldCoefficient_anchor]
    norm_num
  have hsep : ∀ t s, t ≠ s → ∃ j, c t j ≠ c s j := by
    intro t s hts
    exact pkgB2_oldRows_separate T Mint hMcast t s hts
  have hresp : ∀ t s, pkgB2_activeRow T t s → ρ t s ≠ 0 := by
    intro t s hactive
    exact pkgB2_responseField_nonzero_of_active T Mint direction hMcast
      (fun s => (hdirMod s).1) (fun s ω' hω => (hdirMod s).2 ω' hω)
      t s (by simpa [pkgB2_activeRow] using hactive)
  have hne :
      (pkgB2_occurrenceEnum T E) u ≠ (pkgB2_occurrenceEnum T E) v := by
    intro hEq
    exact huv ((pkgB2_occurrenceEnum T E).injective hEq)
  obtain ⟨j, hj⟩ := pkgB2_copies_pairwise_minor c ρ (pkgB2_activeRow T) E
    (.inl ()) ha hsep hresp ((pkgB2_occurrenceEnum T E) u)
      ((pkgB2_occurrenceEnum T E) v) hne
  let i0 := (pkgB2_coordEnum T).symm (.inl (.inl ()))
  let j0 := (pkgB2_coordEnum T).symm j
  have hu0 : rationalResidue r hr
      (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u i0) = 1 := by
    simpa [i0] using pkgB2_rowCoefficientArray_root_residue
      MS T hT J0 gap direction E N p u r hr
  have hv0 : rationalResidue r hr
      (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p v i0) = 1 := by
    simpa [i0] using pkgB2_rowCoefficientArray_root_residue
      MS T hT J0 gap direction E N p v r hr
  have huj : rationalResidue r hr
      (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p u j0) =
        pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) u) j := by
    calc
      _ = pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) u) ((pkgB2_coordEnum T) j0) :=
        pkgB2_rowCoefficientArray_residue_eq_copyCoeff
          MS T hT J0 gap direction E N p u j0 r hr
      _ = pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) u) j := by
        rw [show (pkgB2_coordEnum T) j0 = j by simp [j0]]
  have hvj : rationalResidue r hr
      (pkgB2_rowCoefficientArray MS T hT J0 gap direction E N p v j0) =
        pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) v) j := by
    calc
      _ = pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) v) ((pkgB2_coordEnum T) j0) :=
        pkgB2_rowCoefficientArray_residue_eq_copyCoeff
          MS T hT J0 gap direction E N p v j0 r hr
      _ = pkgB2_copyCoeff c ρ (pkgB2_activeRow T) E
          ((pkgB2_occurrenceEnum T E) v) j := by
        rw [show (pkgB2_coordEnum T) j0 = j by simp [j0]]
  refine ⟨i0, j0, ?_⟩
  have hcopy := hj
  simp only [pkgB2_copyCoeff_anchor c ρ (pkgB2_activeRow T) E (.inl ()) ha] at hcopy
  rw [hu0, hv0, huj, hvj]
  exact hcopy

noncomputable def pkgB2_weightedLinearFormsData {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate)
    (J0 : Fin b → ℕ) (hgap : ∀ k, ValidGap B (gap k))
    (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) :
    WeightedLinearFormsData (q := Fintype.card (pkgB2_Occurrence T E))
      (d := Fintype.card (pkgB2_Coord T)) (b := K)
      (pkgB2_repScales MS T hT) := by
  classical
  let N0 := pkgB2_directionConstantBound T direction + 1
  let V : ℕ → ℕ := pkgB2_blockScale MS.core.parameters B
  let good : ℕ → (Fin (b * sl) → ℕ) → Prop := fun N p =>
    N0 ≤ N ∧ pkgB2_baseRegular MS B T J0 gap hT N p
  refine
    { gap := pkgB2_repGap gap
      rowCoeff := pkgB2_rowCoefficientArray MS T hT J0 gap direction E
      divisor := pkgB2_divisorFamily B U
      V := V
      epsilonBase := pkgB2_epsilonBase MS B T J0 gap hT E
      epsilonCRT := pkgB2_epsilonCRT MS gap
      baseMass := pkgB2_baseMass MS B T J0 gap hT
      goodDomain := good
      epsilonBase_nonnegative := ?_
      V_lower := ?_
      V_tendsto := ?_
      slot_gap_bound := ?_
      base_nonnegative := ?_
      base_normalized := ?_
      divisor_positive := ?_
      divisor_bounded := ?_
      base_residue_uniform := ?_
      row_integer_on_support := ?_
      row_denominators_are_units := ?_
      row_primitive := ?_
      pairwise_row_tests := ?_
      crt_error_bound := ?_
      epsilonBase_superpolynomial := ?_
      epsilonCRT_superpolynomial := ?_ }
  · intro N
    exact pkgB2_epsilonBase_nonneg MS B T J0 gap hT E N
  · intro N
    change MS.core.parameters.M N ≤ pkgB2_blockScale MS.core.parameters B N
    dsimp [pkgB2_blockScale]
    omega
  · exact pkgB2_blockScale_tendsto MS.core.parameters B
  · intro N i
    change pkgB2_blockScale MS.core.parameters B N ≤
      masterScaleV MS.core.parameters N
        (gap ((finProdFinEquiv (m := b) (n := sl)).symm i).1)
    exact pkgB2_blockScale_le_masterScaleV MS.core.parameters B
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm i).1)
      (hgap ((finProdFinEquiv (m := b) (n := sl)).symm i).1).1 N
  · intro N p x
    by_cases hreg : pkgB2_baseRegular MS B T J0 gap hT N p
    · simp [pkgB2_baseMass, hreg]
      exact Finset.prod_nonneg fun i hi =>
        pkgB2_baseCoordinateLaw_nonneg MS B T J0 gap hT N p
          (pkgB2_coordEnum T i) (x i)
    · by_cases hx : x = 0 <;> simp [pkgB2_baseMass, hreg, hx]
  · intro N p
    exact pkgB2_baseMass_tsum_one MS B T J0 gap hT N p
  · intro N u σ hσ
    exact (pkgB2_divisorFamily_support_specs MS B U u N σ hσ).1
  · intro N u σ hσ
    exact (pkgB2_divisorFamily_support_specs MS B U u N σ hσ).2.1
  · intro N p σ hgood hσ hσpos
    rcases hgood with ⟨hN, hreg⟩
    exact pkgB2_baseResidue_uniform MS B T J0 gap hgap hJ0 hT E N p hreg U σ hσ
  · intro N p x hgood hmass u
    exact pkgB2_linearRowValue_den_eq_one MS T hT J0 gap direction E N p u x
  · intro N p hgood r hr hrN hrV u j
    rw [pkgB2_rowCoefficientArray_den_eq_one]
    exact Nat.coprime_one_left r
  · intro N p hgood r hr hrN hrV u
    let j0 := (pkgB2_coordEnum T).symm (.inl (.inl ()))
    refine ⟨j0, ?_⟩
    rw [pkgB2_rowCoefficientArray_anchor]
    letI : Fact r.Prime := ⟨hr⟩
    simp [rationalResidue]
  · intro N p hgood r hr hrN hrV hno u v huv
    rcases hgood with ⟨hN, hreg⟩
    exact pkgB2_pairwiseRowTests MS T hT J0 gap direction hdir E N p
      hN r hr hrN hno u v huv
  · intro N
    exact pkgB2_CRTError_bound MS B gap hgap N
  · exact pkgB2_epsilonBase_superPolynomial MS B T J0 gap hgap hJ0 hT
      (gap k0) (hgap k0) E
  · exact pkgB2_epsilonCRT_superPolynomial MS B gap hgap

/-- The joint event that every replica prime tuple is good, under the disjoint master-slot
embedding. -/
def pkgB2_goodPrimeEvent {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (p : Fin (b * sl) → ℕ) : Prop :=
  ∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)

/-- Value of the translated affine row indexed by one occurrence copy. -/
noncomputable def pkgB2_stateRowValue {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ) (p : Fin (b * sl) → ℕ)
    (o : Fin (Fintype.card (pkgB2_Occurrence T E)))
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) : ℤ :=
  (linearRowValue (pkgB2_rowCoefficientArray MS T hT J0 gap direction E)
    N p o x).num

private theorem pkgB2_linearRowValue_update_eq {q d m : ℕ}
    (rowCoeff : ℕ → (Fin m → ℕ) → Fin q → Fin d → ℚ)
    (N : ℕ) (p : Fin m → ℕ) (u : Fin q) (j0 : Fin d)
    (x : Fin d → ℤ) (z : ℤ) (hzero : rowCoeff N p u j0 = 0) :
    linearRowValue rowCoeff N p u (Function.update x j0 z) =
      linearRowValue rowCoeff N p u x := by
  classical
  unfold linearRowValue
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = j0
  · subst j
    simp [hzero]
  · rw [Function.update_of_ne h]

private theorem pkgB2_stateRowValue_update_own {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (T : Fin b → CubeTemplate)
    (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ) (gap : Fin b → Fin K)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (u : Fin (Fintype.card (pkgB2_Occurrence T E))) (r : pkgB2_Nonroot T)
    (hrow : (pkgB2_occurrenceEnum T E u).1 = Sum.inr r)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) (z : ℤ) :
    pkgB2_stateRowValue MS T hT J0 gap direction E N p u x =
      pkgB2_stateRowValue MS T hT J0 gap direction E N p u
        (Function.update x ((pkgB2_coordEnum T).symm (.inr (r, (0 : Fin 2)))) z) := by
  unfold pkgB2_stateRowValue
  apply congrArg (fun q : ℚ => q.num)
  exact (pkgB2_linearRowValue_update_eq
    (pkgB2_rowCoefficientArray MS T hT J0 gap direction E) N p u
    ((pkgB2_coordEnum T).symm (.inr (r, (0 : Fin 2)))) x z
    (pkgB2_rowCoefficientArray_ownDirection_zero MS T hT J0 gap direction hdir
      E N p u r hrow)).symm

/-- The row product after a set of translation directions has been eliminated. The eliminated
nonroot rows carry their Cauchy–Schwarz weight `(1+ν)`; the remaining rows retain the user `g`. -/
noncomputable def pkgB2_stateFactor {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ)
    (o : Fin (Fintype.card (pkgB2_Occurrence T E))) : ℝ := by
  classical
  let t := (pkgB2_occurrenceEnum T E o).1
  let y := pkgB2_stateRowValue MS T hT J0 gap direction E N p o x
  exact match t with
    | .inl _ => nu MS.core.parameters N B y - 1
    | .inr r =>
        if r ∈ E then 1 + nu MS.core.parameters N B y
        else (I r.1).g r.2.1 (pkgB2_repPrimeProject hT p r.1) y

private noncomputable def pkgB2_stateRowProduct {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) (r : pkgB2_Nonroot T) : ℝ :=
  ∏ o ∈ (Finset.univ.filter fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
      (pkgB2_occurrenceEnum T E o).1 = Sum.inr r),
    pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o

private noncomputable def pkgB2_stateOtherProduct {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) (r : pkgB2_Nonroot T) : ℝ :=
  ∏ o ∈ (Finset.univ.filter fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
      (pkgB2_occurrenceEnum T E o).1 ≠ Sum.inr r),
    pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o

private theorem pkgB2_stateRowProduct_update_own {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (E : Finset (pkgB2_Nonroot T))
    (N : ℕ) (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) (z : ℤ) (r : pkgB2_Nonroot T) :
    pkgB2_stateRowProduct MS B gap T hT J0 direction E N I p x r =
      pkgB2_stateRowProduct MS B gap T hT J0 direction E N I p
        (Function.update x ((pkgB2_coordEnum T).symm (.inr (r, (0 : Fin 2)))) z) r := by
  classical
  unfold pkgB2_stateRowProduct
  apply Finset.prod_congr rfl
  intro o ho
  have hrow := (Finset.mem_filter.mp ho).2
  simp only [pkgB2_stateFactor, hrow]
  rw [pkgB2_stateRowValue_update_own MS T hT J0 gap direction hdir E N p o r hrow x z]

noncomputable def pkgB2_stateIntegrand {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) : ℝ := by
  classical
  exact (if E = ∅ then ∏ k : Fin b, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
    ∏ o, pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o

private theorem pkgB2_stateIntegrand_splitRow {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) (r : pkgB2_Nonroot T) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p x =
      (if E = ∅ then ∏ k : Fin b, (I k).e (pkgB2_repPrimeProject hT p k) else 1) *
        pkgB2_stateRowProduct MS B gap T hT J0 direction E N I p x r *
          pkgB2_stateOtherProduct MS B gap T hT J0 direction E N I p x r := by
  classical
  unfold pkgB2_stateIntegrand pkgB2_stateRowProduct pkgB2_stateOtherProduct
  rw [(Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
      (pkgB2_occurrenceEnum T E o).1 = Sum.inr r)
    (fun o => pkgB2_stateFactor MS B gap T hT J0 direction E N I p x o)).symm]
  ring

/-- The normalized expectation of a translated state over independent replica primes and the
mixed base-coordinate law. At `E=∅` it still includes the original bounded prime factors. -/
noncomputable def pkgB2_stateAverage {K sl b : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (N : ℕ)
    (I : ∀ k, DualInput MS B (T k) N) : ℝ := by
  classical
  let D := pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
    direction hdir k0 E (∅ : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))))
  let Good := pkgB2_goodPrimeEvent MS gap T hT N
  let P := independentPrimePoolProbability
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) Good
  exact P⁻¹ * ∑' p : Fin (b * sl) → ℕ,
    independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p *
      (if Good p then ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
        D.baseMass N p x * pkgB2_stateIntegrand MS B gap T hT J0 direction E N I p x
        else 0)

private def pkgB2_occurrenceIsNonroot {b : ℕ} {T : Fin b → CubeTemplate}
    (E : Finset (pkgB2_Nonroot T))
    (o : Fin (Fintype.card (pkgB2_Occurrence T E))) : Prop :=
  match (pkgB2_occurrenceEnum T E o).1 with
  | .inl _ => False
  | .inr _ => True

private noncomputable def pkgB2_nonrootOccurrenceSet {b : ℕ} {T : Fin b → CubeTemplate}
    (E : Finset (pkgB2_Nonroot T)) : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
  Finset.univ.filter (pkgB2_occurrenceIsNonroot E)

private noncomputable def pkgB2_rootOccurrenceSet {b : ℕ} {T : Fin b → CubeTemplate}
    (E : Finset (pkgB2_Nonroot T)) : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
  Finset.univ.filter (fun o => ¬ pkgB2_occurrenceIsNonroot E o)

private theorem pkgB2_weightedGoodMonomial_tendsto_one {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k) (hsl : 0 < sl)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) :
    Tendsto
      (fun N : ℕ =>
        weightedLinearFormsAverage
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)) /
          weightedLinearFormsEventProbability
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)))
      atTop (𝓝 1) := by
  classical
  let D := pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
    direction hdir k0 E U
  let good (N : ℕ) (p : Fin (b * sl) → ℕ) : Prop :=
    ∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)
  let prob (N : ℕ) : ℝ := weightedLinearFormsEventProbability D N (good N)
  let average (N : ℕ) : ℝ := weightedLinearFormsAverage D N (good N)
  let c : ℝ := (1 / 2 : ℝ) ^ b
  have hc : 0 < c := by dsimp [c]; positivity
  have hgoodDomain : ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      good N p → D.goodDomain N p := by
    have hreg := pkgB2_baseRegular_of_allGood_eventually MS B gap T J0 hgap hT hJ0
    have hN0 : ∀ᶠ N : ℕ in atTop,
        pkgB2_directionConstantBound T direction + 1 ≤ N :=
      eventually_ge_atTop _
    filter_upwards [hreg, hN0] with N hregN hN0 p hp
    change pkgB2_directionConstantBound T direction + 1 ≤ N ∧
      pkgB2_baseRegular MS B T J0 gap hT N p
    exact ⟨hN0, hregN p hp⟩
  obtain ⟨C, hC, hlinear⟩ := prop_linear_forms D
  have herr : Tendsto
      (fun N : ℕ => C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
        Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)))
      atTop (𝓝 0) := by
    have hCconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa using hCconst.mul (weighted_linear_forms_error_tends_zero D)
  have hlinearEventually : ∀ᶠ N : ℕ in atTop,
      |average N - prob N| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
          Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)) := by
    filter_upwards [hgoodDomain] with N hN
    exact hlinear N (good N) (fun p hp => hN p hp)
  have habs : Tendsto (fun N => |average N - prob N|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      hlinearEventually herr
  have hrepLower : ∀ᶠ N : ℕ in atTop, c ≤
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) :=
    pkgB2_repGoodProbability_lower_eventually MS gap T hT hsl
  have hprobEq (N : ℕ) : prob N =
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) := by
    simp [prob, good, weightedLinearFormsEventProbability, D,
      pkgB2_weightedLinearFormsData, pkgB2_repScales, pkgB2_repScalesOfFacts]
  have hprobLower : ∀ᶠ N : ℕ in atTop, c ≤ prob N := by
    filter_upwards [hrepLower] with N hN
    rw [hprobEq]
    exact hN
  have hratioBound (N : ℕ) (hP : c ≤ prob N) :
      |average N / prob N - 1| ≤ |average N - prob N| / c := by
    have hPpos : 0 < prob N := lt_of_lt_of_le hc hP
    have heq : average N / prob N - 1 = (average N - prob N) / prob N := by
      field_simp [ne_of_gt hPpos]
    rw [heq, abs_div, abs_of_pos hPpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hP
  have hratioError : Tendsto (fun N => |average N - prob N| / c) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using habs.mul_const c⁻¹
  have hratio : Tendsto (fun N => |average N / prob N - 1|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      (Filter.Eventually.mono hprobLower (fun N hP => hratioBound N hP)) hratioError
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa [Real.norm_eq_abs, average, prob, D, good] using hratio

/-- Expand the retained `(1+v)` factors and root `(v-1)` factors into divisor monomials.
The sign is factored as `(-1)^|minus| * (-1)^|M|`, which avoids subtraction on cardinalities. -/
theorem pkgB2_signedProductExpansion {α : Type*} [DecidableEq α]
    (plus minus : Finset α) (hdisj : Disjoint plus minus) (v : α → ℝ) :
    (∏ a ∈ plus, (1 + v a)) * (∏ a ∈ minus, (v a - 1)) =
      ∑ P ∈ plus.powerset, ∑ M ∈ minus.powerset,
        (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card * ∏ a ∈ P ∪ M, v a := by
  classical
  let pPow := plus.powerset
  let mPow := minus.powerset
  have hplus : ∏ a ∈ plus, (1 + v a) =
      ∑ P ∈ pPow, ∏ a ∈ P, v a := by
    simpa [pPow] using (Finset.prod_one_add (f := v) (s := plus))
  have hminus : ∏ a ∈ minus, (v a - 1) =
      (-1 : ℝ) ^ minus.card *
        ∑ M ∈ mPow, (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a := by
    have hsub : ∏ a ∈ minus, (1 - v a) =
        ∑ M ∈ mPow, ∏ a ∈ M, (-v a) := by
      simpa [mPow, sub_eq_add_neg] using
        (Finset.prod_one_add (f := fun a => -v a) (s := minus))
    have hprodNeg (M : Finset α) (hM : M ∈ mPow) :
        ∏ a ∈ M, (-v a) = (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a := by
      calc
        ∏ a ∈ M, (-v a) = ∏ a ∈ M, ((-1 : ℝ) * v a) := by
          apply Finset.prod_congr rfl
          intro a ha
          ring
        _ = (∏ _a ∈ M, (-1 : ℝ)) * ∏ a ∈ M, v a := Finset.prod_mul_distrib
        _ = (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a := by simp
    have hsub' : ∏ a ∈ minus, (1 - v a) =
        ∑ M ∈ mPow, (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a := by
      rw [hsub]
      apply Finset.sum_congr rfl
      intro M hM
      exact hprodNeg M hM
    have hneg : ∏ a ∈ minus, (v a - 1) =
        (-1 : ℝ) ^ minus.card * ∏ a ∈ minus, (1 - v a) := by
      rw [show (∏ a ∈ minus, (v a - 1)) =
        ∏ a ∈ minus, ((-1 : ℝ) * (1 - v a)) by
          apply Finset.prod_congr rfl
          intro a ha
          ring]
      rw [Finset.prod_mul_distrib]
      simp
    rw [hneg, hsub']
  rw [hplus, hminus]
  simp only [pPow, mPow]
  calc
    (∑ P ∈ plus.powerset, ∏ a ∈ P, v a) *
        ((-1 : ℝ) ^ minus.card *
          ∑ M ∈ minus.powerset, (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a) =
      ∑ P ∈ plus.powerset, ∑ M ∈ minus.powerset,
        (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card *
          (∏ a ∈ P, v a) * (∏ a ∈ M, v a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P hP
      calc
        (∏ a ∈ P, v a) *
            ((-1 : ℝ) ^ minus.card *
              ∑ M ∈ minus.powerset, (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a) =
          ((-1 : ℝ) ^ minus.card * ∏ a ∈ P, v a) *
            ∑ M ∈ minus.powerset, (-1 : ℝ) ^ M.card * ∏ a ∈ M, v a := by ring
        _ = ∑ M ∈ minus.powerset,
            ((-1 : ℝ) ^ minus.card * ∏ a ∈ P, v a) *
              ((-1 : ℝ) ^ M.card * ∏ a ∈ M, v a) := by rw [Finset.mul_sum]
        _ = ∑ M ∈ minus.powerset,
            (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card *
              (∏ a ∈ P, v a) * (∏ a ∈ M, v a) := by
          apply Finset.sum_congr rfl
          intro M hM
          ring
    _ = ∑ P ∈ plus.powerset, ∑ M ∈ minus.powerset,
        (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card * ∏ a ∈ P ∪ M, v a := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro M hM
      have hPM : Disjoint P M :=
        hdisj.mono (Finset.mem_powerset.mp hP) (Finset.mem_powerset.mp hM)
      rw [Finset.prod_union hPM]
      ring

private theorem pkgB2_terminalStateIntegrand_signedExpansion {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (J0 : Fin b → ℕ)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (N : ℕ) (I : ∀ k, DualInput MS B (T k) N)
    (p : Fin (b * sl) → ℕ) (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ)
    (hNonroot : Nonempty (pkgB2_Nonroot T)) :
    pkgB2_stateIntegrand MS B gap T hT J0 direction Finset.univ N I p x =
      ∑ P ∈ (pkgB2_nonrootOccurrenceSet (T := T) Finset.univ).powerset,
        ∑ M ∈ (pkgB2_rootOccurrenceSet (T := T) Finset.univ).powerset,
          (-1 : ℝ) ^ (pkgB2_rootOccurrenceSet (T := T) Finset.univ).card *
            (-1 : ℝ) ^ M.card *
              ∏ o ∈ P ∪ M,
                nu MS.core.parameters N B
                  (pkgB2_stateRowValue MS T hT J0 gap direction Finset.univ N p o x) := by
  classical
  let plus := pkgB2_nonrootOccurrenceSet (T := T) Finset.univ
  let minus := pkgB2_rootOccurrenceSet (T := T) Finset.univ
  let v : Fin (Fintype.card (pkgB2_Occurrence T Finset.univ)) → ℝ := fun o =>
    nu MS.core.parameters N B
      (pkgB2_stateRowValue MS T hT J0 gap direction Finset.univ N p o x)
  have hE : (Finset.univ : Finset (pkgB2_Nonroot T)) ≠ ∅ := by
    have hU : (Finset.univ : Finset (pkgB2_Nonroot T)).Nonempty := by
      rcases hNonroot with ⟨r⟩
      exact ⟨r, Finset.mem_univ r⟩
    exact hU.ne_empty
  have hdisj : Disjoint plus minus := by
    rw [Finset.disjoint_left]
    intro o ho hm
    exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp ho).2
  have hplus :
      ∏ o ∈ plus, pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o =
        ∏ o ∈ plus, (1 + v o) := by
    apply Finset.prod_congr rfl
    intro o ho
    have hnr := (Finset.mem_filter.mp ho).2
    cases hrow : (pkgB2_occurrenceEnum T Finset.univ o).1 with
    | inl a =>
        simp [pkgB2_occurrenceIsNonroot, hrow] at hnr
    | inr r =>
        simp [pkgB2_occurrenceIsNonroot, hrow] at hnr
        have hrow' : ((Fintype.equivFin (pkgB2_Occurrence T Finset.univ)).symm o).1 =
            Sum.inr r := by simpa [pkgB2_occurrenceEnum] using hrow
        simp [pkgB2_stateFactor, hrow, hrow', v, Finset.mem_univ]
  have hminus :
      ∏ o ∈ minus, pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o =
        ∏ o ∈ minus, (v o - 1) := by
    apply Finset.prod_congr rfl
    intro o ho
    have hroot := (Finset.mem_filter.mp ho).2
    cases hrow : (pkgB2_occurrenceEnum T Finset.univ o).1 with
    | inl a =>
        simp [pkgB2_occurrenceIsNonroot, hrow] at hroot
        have hrow' : ((Fintype.equivFin (pkgB2_Occurrence T Finset.univ)).symm o).1 =
            Sum.inl a := by simpa [pkgB2_occurrenceEnum] using hrow
        simp [pkgB2_stateFactor, hrow, hrow', v, Finset.mem_univ]
    | inr r =>
        simp [pkgB2_occurrenceIsNonroot, hrow] at hroot
  have hsplit :
      ∏ o : Fin (Fintype.card (pkgB2_Occurrence T Finset.univ)),
        pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o =
      (∏ o ∈ plus, pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o) *
        ∏ o ∈ minus, pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o := by
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
      (pkgB2_occurrenceIsNonroot (T := T) Finset.univ)
      (fun o => pkgB2_stateFactor MS B gap T hT J0 direction Finset.univ N I p x o)).symm
  have hstate :
      pkgB2_stateIntegrand MS B gap T hT J0 direction Finset.univ N I p x =
        (∏ o ∈ plus, (1 + v o)) * ∏ o ∈ minus, (v o - 1) := by
    unfold pkgB2_stateIntegrand
    simp only [if_neg (by simpa [hE] : Finset.univ ≠ (∅ : Finset (pkgB2_Nonroot T))), one_mul]
    rw [hsplit, hplus, hminus]
  rw [hstate]
  simpa [plus, minus, v] using pkgB2_signedProductExpansion plus minus hdisj v


private theorem pkgB2_alternatingPowersetSum_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    ∑ M ∈ s.powerset, (-1 : ℝ) ^ M.card = 0 := by
  have hz : ∑ M ∈ s.powerset, (-1 : ℤ) ^ M.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  exact_mod_cast hz

/-- Once every divisor monomial has the same main term, the final signed expansion cancels it;
the remaining finite sum is bounded by the number of subset pairs times a uniform error. -/
theorem pkgB2_signedMomentError_bound {α : Type*} [DecidableEq α]
    (plus minus : Finset α) (P : ℝ) (moment : Finset α → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hmain : ∀ U, |moment U - P| ≤ ε) (hminus : minus.Nonempty) :
    |∑ A ∈ plus.powerset, ∑ M ∈ minus.powerset,
        (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card * moment (A ∪ M)| ≤
      (2 : ℝ) ^ (plus.card + minus.card) * ε := by
  classical
  let Pset := plus.powerset
  let Mset := minus.powerset
  let c : Finset α → ℝ := fun M => (-1 : ℝ) ^ minus.card * (-1 : ℝ) ^ M.card
  have hcAbs (M : Finset α) : |c M| = 1 := by simp [c]
  have hcSum : ∑ M ∈ Mset, c M = 0 := by
    calc
      ∑ M ∈ Mset, c M =
          (-1 : ℝ) ^ minus.card * ∑ M ∈ Mset, (-1 : ℝ) ^ M.card := by
            simp only [c]
            rw [← Finset.mul_sum]
      _ = 0 := by
        simp [Mset, pkgB2_alternatingPowersetSum_zero minus hminus]
  have hconstant :
      ∑ A ∈ Pset, ∑ M ∈ Mset, c M * P = 0 := by
    have hinner (A : Finset α) : ∑ M ∈ Mset, c M * P = 0 := by
      calc
        ∑ M ∈ Mset, c M * P = (∑ M ∈ Mset, c M) * P := by rw [Finset.sum_mul]
        _ = 0 := by rw [hcSum]; simp
    calc
      ∑ A ∈ Pset, ∑ M ∈ Mset, c M * P = ∑ A ∈ Pset, 0 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact hinner A
      _ = 0 := by simp
  have hsplit :
      (∑ A ∈ Pset, ∑ M ∈ Mset, c M * moment (A ∪ M)) =
        (∑ A ∈ Pset, ∑ M ∈ Mset, c M * P) +
          ∑ A ∈ Pset, ∑ M ∈ Mset, c M * (moment (A ∪ M) - P) := by
    simp_rw [show ∀ A M, c M * moment (A ∪ M) =
      c M * P + c M * (moment (A ∪ M) - P) from by intro A M; ring,
      Finset.sum_add_distrib]
  have hboundM (A : Finset α) :
      |∑ M ∈ Mset, c M * (moment (A ∪ M) - P)| ≤
        (Mset.card : ℝ) * ε := by
    calc
      |∑ M ∈ Mset, c M * (moment (A ∪ M) - P)| ≤
          ∑ M ∈ Mset, |c M * (moment (A ∪ M) - P)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _M ∈ Mset, ε := by
        apply Finset.sum_le_sum
        intro M hM
        rw [abs_mul, hcAbs, one_mul]
        exact hmain (A ∪ M)
      _ = (Mset.card : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  have hboundA :
      |∑ A ∈ Pset, ∑ M ∈ Mset, c M * (moment (A ∪ M) - P)| ≤
        (Pset.card : ℝ) * (Mset.card : ℝ) * ε := by
    calc
      _ ≤ ∑ A ∈ Pset,
          |∑ M ∈ Mset, c M * (moment (A ∪ M) - P)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _A ∈ Pset, (Mset.card : ℝ) * ε := by
        apply Finset.sum_le_sum
        intro A hA
        exact hboundM A
      _ = (Pset.card : ℝ) * (Mset.card : ℝ) * ε := by
        calc
          ∑ _A ∈ Pset, (Mset.card : ℝ) * ε =
              (Pset.card : ℝ) * ((Mset.card : ℝ) * ε) := by
                simp [Finset.sum_const, nsmul_eq_mul]
          _ = (Pset.card : ℝ) * (Mset.card : ℝ) * ε := by ring
  have hcardP : Pset.card = 2 ^ plus.card := by simp [Pset]
  have hcardM : Mset.card = 2 ^ minus.card := by simp [Mset]
  calc
    |∑ A ∈ Pset, ∑ M ∈ Mset, c M * moment (A ∪ M)| =
        |∑ A ∈ Pset, ∑ M ∈ Mset, c M * (moment (A ∪ M) - P)| := by
          rw [hsplit, hconstant]
          simp
    _ ≤ (Pset.card : ℝ) * (Mset.card : ℝ) * ε := hboundA
    _ = (2 : ℝ) ^ (plus.card + minus.card) * ε := by
      rw [hcardP, hcardM]
      push_cast
      rw [pow_add]


end Prediction
end HindmanSumsProducts
