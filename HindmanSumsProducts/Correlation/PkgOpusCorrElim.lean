import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgElim
import HindmanSumsProducts.Correlation.PkgElim2
import HindmanSumsProducts.Correlation.PkgVarS

/-! Helpers of lane `opus-corr` for the weighted Cauchy–Schwarz part of additive elimination
(04:442–509): the box integrands `Φ_E`, the averaging identities over one shift coordinate, and
the step `|E Φ_E|² ≤ (E Ω)·E Φ_{E∪{R}}`. -/

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Branches supported in a set of directions -/

section Supp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Branch choices `ω : κ → {0,1}` vanishing outside `P`. -/
def opus_corr_supp (P : κ → Prop) : Finset (κ → Fin 2) :=
  Finset.univ.filter fun ω => ∀ x, ¬ P x → ω x = 0

theorem opus_corr_fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

theorem opus_corr_supp_insert (P : κ → Prop) (c : κ) (hc : ¬ P c) :
    opus_corr_supp (fun x => P x ∨ x = c) =
      opus_corr_supp P ∪ (opus_corr_supp P).image (fun ω => Function.update ω c 1) := by
  ext ω
  simp only [opus_corr_supp, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, not_or]
  constructor
  · intro h
    rcases opus_corr_fin2_cases (ω c) with h0 | h1
    · left
      intro x hx
      by_cases hxc : x = c
      · subst x; exact h0
      · exact h x ⟨hx, hxc⟩
    · right
      refine ⟨Function.update ω c 0, ?_, ?_⟩
      · intro x hx
        by_cases hxc : x = c
        · subst x; simp
        · rw [Function.update_of_ne hxc]; exact h x ⟨hx, hxc⟩
      · funext x
        by_cases hxc : x = c
        · subst x; simp [h1]
        · simp [Function.update_of_ne hxc]
  · rintro (h | ⟨ω', h', rfl⟩)
    · intro x hx; exact h x hx.1
    · intro x hx
      rw [Function.update_of_ne hx.2]
      exact h' x hx.1

theorem opus_corr_supp_prod_insert (P : κ → Prop) (c : κ) (hc : ¬ P c)
    (g : (κ → Fin 2) → ℝ) :
    ∏ ω ∈ opus_corr_supp (fun x => P x ∨ x = c), g ω =
      (∏ ω ∈ opus_corr_supp P, g ω) *
        ∏ ω ∈ opus_corr_supp P, g (Function.update ω c 1) := by
  rw [opus_corr_supp_insert P c hc]
  have hzero : ∀ ω ∈ opus_corr_supp P, ω c = 0 := by
    intro ω hω
    simp only [opus_corr_supp, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    exact hω c hc
  rw [Finset.prod_union, Finset.prod_image]
  · intro ω hω ω' hω' heq
    funext x
    by_cases hxc : x = c
    · subst x; rw [hzero ω hω, hzero ω' hω']
    · have := congrFun heq x
      simpa [Function.update_of_ne hxc] using this
  · rw [Finset.disjoint_left]
    intro ω hω hω'
    obtain ⟨ω', hω'', rfl⟩ := Finset.mem_image.mp hω'
    have := hzero _ hω
    simp at this

end Supp

/-! ## Shift assignments: setting one coordinate -/

section ShiftCoord

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `u` with its coordinate `(R,b)` set to `t`. -/
def opus_corr_setc (u : ι → Fin 2 → ℕ) (R : ι) (b : Fin 2) (t : ℕ) : ι → Fin 2 → ℕ :=
  Function.update u R (Function.update (u R) b t)

theorem opus_corr_setc_apply_same (u : ι → Fin 2 → ℕ) (R : ι) (b : Fin 2) (t : ℕ) :
    opus_corr_setc u R b t R b = t := by
  simp [opus_corr_setc]

theorem opus_corr_setc_setc_same (u : ι → Fin 2 → ℕ) (R : ι) (b : Fin 2) (t t' : ℕ) :
    opus_corr_setc (opus_corr_setc u R b t) R b t' = opus_corr_setc u R b t' := by
  funext x c
  by_cases hx : x = R
  · subst x; by_cases hc : c = b
    · subst c; simp [opus_corr_setc]
    · simp [opus_corr_setc, Function.update_of_ne hc]
  · simp [opus_corr_setc, Function.update_of_ne hx]

theorem opus_corr_setc_self (u : ι → Fin 2 → ℕ) (R : ι) (b : Fin 2) :
    opus_corr_setc u R b (u R b) = u := by
  funext x c
  by_cases hx : x = R
  · subst x; by_cases hc : c = b
    · subst c; simp [opus_corr_setc]
    · simp [opus_corr_setc, Function.update_of_ne hc]
  · simp [opus_corr_setc, Function.update_of_ne hx]

theorem opus_corr_setc_comm (u : ι → Fin 2 → ℕ) (R : ι) (b b' : Fin 2) (hbb : b ≠ b')
    (t t' : ℕ) :
    opus_corr_setc (opus_corr_setc u R b t) R b' t' =
      opus_corr_setc (opus_corr_setc u R b' t') R b t := by
  funext x c
  by_cases hx : x = R
  · subst x
    by_cases hc : c = b
    · subst c; simp [opus_corr_setc, Function.update_of_ne hbb]
    · by_cases hc' : c = b'
      · subst c; simp [opus_corr_setc, Function.update_of_ne (Ne.symm hbb)]
      · simp [opus_corr_setc, Function.update_of_ne hc, Function.update_of_ne hc']
  · simp [opus_corr_setc, Function.update_of_ne hx]

/-- The box `[0,L)^{ι×2}` of shift assignments. -/
def opus_corr_box (L : ℕ) : Finset (ι → Fin 2 → ℕ) :=
  Fintype.piFinset fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L

theorem opus_corr_setc_mem_box {L : ℕ} {u : ι → Fin 2 → ℕ} (hu : u ∈ opus_corr_box L)
    (R : ι) (b : Fin 2) {t : ℕ} (ht : t < L) : opus_corr_setc u R b t ∈ opus_corr_box L := by
  simp only [opus_corr_box, Fintype.mem_piFinset, Finset.mem_range] at hu ⊢
  intro x c
  by_cases hx : x = R
  · subst x; by_cases hc : c = b
    · subst c; simp [opus_corr_setc, ht]
    · simp [opus_corr_setc, Function.update_of_ne hc, hu]
  · simp [opus_corr_setc, Function.update_of_ne hx, hu]

/-- Averaging one coordinate of the box does not change the sum. -/
theorem opus_corr_box_sum_coord (L : ℕ) (R : ι) (b : Fin 2) (F : (ι → Fin 2 → ℕ) → ℝ) :
    ∑ u ∈ opus_corr_box L, ∑ t ∈ Finset.range L, F (opus_corr_setc u R b t) =
      (L : ℝ) * ∑ u ∈ opus_corr_box L, F u := by
  rw [← Finset.sum_product' (f := fun u t => F (opus_corr_setc u R b t))]
  have hbij : ∑ x ∈ opus_corr_box L ×ˢ Finset.range L, F (opus_corr_setc x.1 R b x.2) =
      ∑ x ∈ opus_corr_box L ×ˢ Finset.range L, F x.1 := by
    apply Finset.sum_nbij' (fun x => (opus_corr_setc x.1 R b x.2, x.1 R b))
      (fun x => (opus_corr_setc x.1 R b x.2, x.1 R b))
    · intro x hx
      obtain ⟨hu, ht⟩ := Finset.mem_product.mp hx
      refine Finset.mem_product.mpr ⟨opus_corr_setc_mem_box hu R b (Finset.mem_range.mp ht), ?_⟩
      simp only [opus_corr_box, Fintype.mem_piFinset, Finset.mem_range] at hu
      exact Finset.mem_range.mpr (hu R b)
    · intro x hx
      obtain ⟨hu, ht⟩ := Finset.mem_product.mp hx
      refine Finset.mem_product.mpr ⟨opus_corr_setc_mem_box hu R b (Finset.mem_range.mp ht), ?_⟩
      simp only [opus_corr_box, Fintype.mem_piFinset, Finset.mem_range] at hu
      exact Finset.mem_range.mpr (hu R b)
    · intro x _
      simp only [opus_corr_setc_apply_same, opus_corr_setc_setc_same, opus_corr_setc_self]
    · intro x _
      simp only [opus_corr_setc_apply_same, opus_corr_setc_setc_same, opus_corr_setc_self]
    · intro x _
      simp only [opus_corr_setc_setc_same, opus_corr_setc_self]
  rw [hbij, Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem opus_corr_shiftAverage_eq_box (L : ℕ) (F : (ι → Fin 2 → ℕ) → ℝ) :
    shiftAverage ι L F = ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ * ∑ u ∈ opus_corr_box L, F u := rfl

theorem opus_corr_box_empty {L : ℕ} (hL : L = 0) (R : ι) : opus_corr_box (ι := ι) L = ∅ := by
  subst hL
  ext u
  simp only [opus_corr_box, Fintype.mem_piFinset, Finset.mem_range, Finset.notMem_empty,
    iff_false, not_forall, not_lt]
  exact ⟨R, 0, Nat.zero_le _⟩

/-- `E[H_out H_in] = E[H_out·E_{u_R^0}H_in]` when `H_out` does not depend on `u_R^0`. -/
theorem opus_corr_shiftAverage_avg_coord (L : ℕ) (R : ι) (Hout Hin : (ι → Fin 2 → ℕ) → ℝ)
    (hout : ∀ u t, Hout (opus_corr_setc u R 0 t) = Hout u) :
    shiftAverage ι L (fun u => Hout u * Hin u) =
      shiftAverage ι L (fun u => Hout u *
        ((L : ℝ)⁻¹ * ∑ t ∈ Finset.range L, Hin (opus_corr_setc u R 0 t))) := by
  rw [opus_corr_shiftAverage_eq_box, opus_corr_shiftAverage_eq_box]
  congr 1
  by_cases hL : L = 0
  · rw [opus_corr_box_empty hL R]; simp
  have hLpos : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have key := opus_corr_box_sum_coord L R 0 (fun u => Hout u * Hin u)
  simp only [hout] at key
  calc
    ∑ u ∈ opus_corr_box L, Hout u * Hin u =
        (L : ℝ)⁻¹ * ((L : ℝ) * ∑ u ∈ opus_corr_box L, Hout u * Hin u) := by
      field_simp
    _ = (L : ℝ)⁻¹ * ∑ u ∈ opus_corr_box L, ∑ t ∈ Finset.range L,
          Hout u * Hin (opus_corr_setc u R 0 t) := by rw [key]
    _ = ∑ u ∈ opus_corr_box L, Hout u *
          ((L : ℝ)⁻¹ * ∑ t ∈ Finset.range L, Hin (opus_corr_setc u R 0 t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- `E[Ω H_in(u_R^0) H_in(u_R^1)] = E[Ω (E_t H_in)²]` when `Ω` does not depend on `u_R` and
`H_in` does not depend on `u_R^1`. -/
theorem opus_corr_shiftAverage_square_coord (L : ℕ) (R : ι) (Ω Hin : (ι → Fin 2 → ℕ) → ℝ)
    (hΩ0 : ∀ u t, Ω (opus_corr_setc u R 0 t) = Ω u)
    (hΩ1 : ∀ u t, Ω (opus_corr_setc u R 1 t) = Ω u)
    (hin1 : ∀ u t, Hin (opus_corr_setc u R 1 t) = Hin u) :
    shiftAverage ι L (fun u => Ω u * Hin u * Hin (opus_corr_setc u R 0 (u R 1))) =
      shiftAverage ι L (fun u => Ω u *
        ((L : ℝ)⁻¹ * ∑ t ∈ Finset.range L, Hin (opus_corr_setc u R 0 t)) ^ 2) := by
  rw [opus_corr_shiftAverage_eq_box, opus_corr_shiftAverage_eq_box]
  congr 1
  by_cases hL : L = 0
  · rw [opus_corr_box_empty hL R]; simp
  have hLpos : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let G : (ι → Fin 2 → ℕ) → ℝ := fun u => Ω u * Hin u * Hin (opus_corr_setc u R 0 (u R 1))
  have hG (u : ι → Fin 2 → ℕ) (t t' : ℕ) :
      G (opus_corr_setc (opus_corr_setc u R 0 t) R 1 t') =
        Ω u * Hin (opus_corr_setc u R 0 t) * Hin (opus_corr_setc u R 0 t') := by
    simp only [G]
    rw [hΩ1, hΩ0, hin1, opus_corr_setc_apply_same]
    rw [opus_corr_setc_comm u R 0 1 h01 t t', opus_corr_setc_setc_same]
    rw [opus_corr_setc_comm u R 1 0 (Ne.symm h01) t' t', hin1]
  have k1 := opus_corr_box_sum_coord L R 0 G
  have k2 (t : ℕ) := opus_corr_box_sum_coord L R 1 (fun u => G (opus_corr_setc u R 0 t))
  calc
    ∑ u ∈ opus_corr_box L, G u =
        ((L : ℝ) ^ 2)⁻¹ * ((L : ℝ) * ((L : ℝ) * ∑ u ∈ opus_corr_box L, G u)) := by
      field_simp
    _ = ((L : ℝ) ^ 2)⁻¹ * ((L : ℝ) * ∑ u ∈ opus_corr_box L, ∑ t ∈ Finset.range L,
          G (opus_corr_setc u R 0 t)) := by rw [k1]
    _ = ((L : ℝ) ^ 2)⁻¹ * ∑ u ∈ opus_corr_box L, ∑ t ∈ Finset.range L,
          ∑ t' ∈ Finset.range L, G (opus_corr_setc (opus_corr_setc u R 0 t) R 1 t') := by
      congr 1
      calc
        (L : ℝ) * ∑ u ∈ opus_corr_box L, ∑ t ∈ Finset.range L, G (opus_corr_setc u R 0 t) =
            (L : ℝ) * ∑ t ∈ Finset.range L, ∑ u ∈ opus_corr_box L,
              G (opus_corr_setc u R 0 t) := by rw [Finset.sum_comm]
        _ = ∑ t ∈ Finset.range L, (L : ℝ) * ∑ u ∈ opus_corr_box L,
              G (opus_corr_setc u R 0 t) := by rw [Finset.mul_sum]
        _ = ∑ t ∈ Finset.range L, ∑ u ∈ opus_corr_box L, ∑ t' ∈ Finset.range L,
              G (opus_corr_setc (opus_corr_setc u R 0 t) R 1 t') := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← k2 t]
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro t' _
          rw [opus_corr_setc_comm u R 1 0 (Ne.symm h01) t' t]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ u ∈ opus_corr_box L, Ω u *
          ((L : ℝ)⁻¹ * ∑ t ∈ Finset.range L, Hin (opus_corr_setc u R 0 t)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp_rw [hG]
      have hsq : (∑ t ∈ Finset.range L, Hin (opus_corr_setc u R 0 t)) ^ 2 =
          ∑ t ∈ Finset.range L, ∑ t' ∈ Finset.range L,
            Hin (opus_corr_setc u R 0 t) * Hin (opus_corr_setc u R 0 t') := by
        rw [sq, Finset.sum_mul_sum]
      rw [mul_pow, hsq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t' _
      ring

end ShiftCoord

end
end HindmanSumsProducts
