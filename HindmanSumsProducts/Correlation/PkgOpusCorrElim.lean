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


/-! ## The box integrands `Φ_E` -/

section BoxPhi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Branches supported in `E`. -/
def opus_corr_br (E : Finset ι) : Finset (ι → Fin 2) := opus_corr_supp (fun x => x ∈ E)

/-- Branches of the directions other than `I`, supported in `E`. -/
def opus_corr_brI (E : Finset ι) (I : ι) : Finset ({R // R ≠ I} → Fin 2) :=
  opus_corr_supp (fun x : {R // R ≠ I} => x.1 ∈ E)

/-- The shifts chosen by a branch. -/
def opus_corr_ev (u : ι → Fin 2 → ℕ) (ω : ι → Fin 2) : ι → ℕ := fun R => u R (ω R)

/-- The shifts chosen by a branch of the directions other than `I`. -/
def opus_corr_evI {I : ι} (u : ι → Fin 2 → ℕ) (η : {R // R ≠ I} → Fin 2) :
    {R // R ≠ I} → ℕ := fun R => u R.1 (η R)

/-- The restriction of a branch to the directions other than `I`. -/
def opus_corr_restr (ω : ι → Fin 2) (I : ι) : {R // R ≠ I} → Fin 2 := fun R => ω R.1

/-- `Φ_E`: after eliminating the directions in `E`, the target cube over the branches of `E`,
the active rows `I ∉ E` over the same branches, and the retained weights of the eliminated rows
(04:461–509). -/
def opus_corr_boxPhi (T : (ι → ℕ) → ℝ) (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ)
    (E : Finset ι) (u : ι → Fin 2 → ℕ) : ℝ :=
  (∏ ω ∈ opus_corr_br E, T (opus_corr_ev u ω)) *
    (∏ ω ∈ opus_corr_br E, ∏ I ∈ Finset.univ.filter (fun I => I ∉ E),
      A I (opus_corr_evI u (opus_corr_restr ω I))) *
    ∏ I ∈ E, ∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI u η)

/-- The copies of the row `R` being eliminated. -/
def opus_corr_boxOut (A : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ) (E : Finset ι) (R : ι)
    (u : ι → Fin 2 → ℕ) : ℝ :=
  ∏ ω ∈ opus_corr_br E, A R (opus_corr_evI u (opus_corr_restr ω R))

/-- Their weight bound `Ω_R`. -/
def opus_corr_boxOmega (Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ) (E : Finset ι) (R : ι)
    (u : ι → Fin 2 → ℕ) : ℝ :=
  ∏ η ∈ opus_corr_brI E R, Wt R (opus_corr_evI u η)

/-- All other factors, `H_in`. -/
def opus_corr_boxIn (T : (ι → ℕ) → ℝ) (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ)
    (E : Finset ι) (R : ι) (u : ι → Fin 2 → ℕ) : ℝ :=
  (∏ ω ∈ opus_corr_br E, T (opus_corr_ev u ω)) *
    (∏ ω ∈ opus_corr_br E, ∏ I ∈ Finset.univ.filter (fun I => I ∉ insert R E),
      A I (opus_corr_evI u (opus_corr_restr ω I))) *
    ∏ I ∈ E, ∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI u η)

theorem opus_corr_mem_br {E : Finset ι} {ω : ι → Fin 2} :
    ω ∈ opus_corr_br E ↔ ∀ x, x ∉ E → ω x = 0 := by
  simp [opus_corr_br, opus_corr_supp]

theorem opus_corr_mem_brI {E : Finset ι} {I : ι} {η : {R // R ≠ I} → Fin 2} :
    η ∈ opus_corr_brI E I ↔ ∀ x : {R // R ≠ I}, x.1 ∉ E → η x = 0 := by
  simp [opus_corr_brI, opus_corr_supp]

theorem opus_corr_br_insert (E : Finset ι) (R : ι) :
    opus_corr_br (insert R E) = opus_corr_supp (fun x => x ∈ E ∨ x = R) := by
  unfold opus_corr_br
  congr 1
  funext x
  simp [Finset.mem_insert, or_comm]

theorem opus_corr_brI_insert_self (E : Finset ι) (R : ι) :
    opus_corr_brI (insert R E) R = opus_corr_brI E R := by
  unfold opus_corr_brI
  congr 1
  funext x
  have hx : x.1 ≠ R := x.2
  simp [Finset.mem_insert, hx]

theorem opus_corr_brI_insert_other (E : Finset ι) (R I : ι) (hRI : R ≠ I) :
    opus_corr_brI (insert R E) I =
      opus_corr_supp (fun x : {R // R ≠ I} => x.1 ∈ E ∨ x = ⟨R, hRI⟩) := by
  unfold opus_corr_brI
  congr 1
  funext x
  apply propext
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · right; exact Subtype.ext h
    · left; exact h
  · rintro (h | h)
    · exact Finset.mem_insert_of_mem h
    · rw [h]; exact Finset.mem_insert_self R E

/-- The shift assignment with `u_R^0` replaced by `u_R^1`. -/
def opus_corr_swap (u : ι → Fin 2 → ℕ) (R : ι) : ι → Fin 2 → ℕ :=
  opus_corr_setc u R 0 (u R 1)

theorem opus_corr_ev_update (u : ι → Fin 2 → ℕ) (R : ι) (ω : ι → Fin 2) (hω : ω R = 0) :
    opus_corr_ev u (Function.update ω R 1) = opus_corr_ev (opus_corr_swap u R) ω := by
  funext x
  unfold opus_corr_ev opus_corr_swap opus_corr_setc
  by_cases hx : x = R
  · subst x; simp [hω]
  · simp [Function.update_of_ne hx]

theorem opus_corr_evI_restr_update (u : ι → Fin 2 → ℕ) (R I : ι) (hRI : R ≠ I)
    (ω : ι → Fin 2) (hω : ω R = 0) :
    opus_corr_evI u (opus_corr_restr (Function.update ω R 1) I) =
      opus_corr_evI (opus_corr_swap u R) (opus_corr_restr ω I) := by
  funext x
  unfold opus_corr_evI opus_corr_restr opus_corr_swap opus_corr_setc
  by_cases hx : x.1 = R
  · rw [hx]; simp [hω]
  · simp [Function.update_of_ne hx]

theorem opus_corr_evI_update (u : ι → Fin 2 → ℕ) (R I : ι) (hRI : R ≠ I)
    (η : {R // R ≠ I} → Fin 2) (hη : η ⟨R, hRI⟩ = 0) :
    opus_corr_evI u (Function.update η ⟨R, hRI⟩ 1) = opus_corr_evI (opus_corr_swap u R) η := by
  funext x
  unfold opus_corr_evI opus_corr_swap opus_corr_setc
  by_cases hx : x = ⟨R, hRI⟩
  · subst hx; simp [hη]
  · have hx' : x.1 ≠ R := fun h => hx (Subtype.ext h)
    simp [Function.update_of_ne hx, Function.update_of_ne hx']

/-- `Φ_E = H_out·H_in` for `R ∉ E`. -/
theorem opus_corr_boxPhi_split (T : (ι → ℕ) → ℝ) (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ)
    (E : Finset ι) (R : ι) (hR : R ∉ E) (u : ι → Fin 2 → ℕ) :
    opus_corr_boxPhi T A Wt E u =
      opus_corr_boxOut A E R u * opus_corr_boxIn T A Wt E R u := by
  have hfilter : Finset.univ.filter (fun I => I ∉ E) =
      insert R (Finset.univ.filter (fun I => I ∉ insert R E)) := by
    ext I
    by_cases hI : I = R
    · subst I; simp [hR]
    · simp [hI]
  have hRnot : R ∉ Finset.univ.filter (fun I => I ∉ insert R E) := by simp
  unfold opus_corr_boxPhi opus_corr_boxOut opus_corr_boxIn
  rw [hfilter]
  simp_rw [Finset.prod_insert hRnot]
  rw [Finset.prod_mul_distrib]
  ring

/-- `Φ_{E∪{R}} = Ω_R·H_in·H_in(u_R^0 := u_R^1)` for `R ∉ E` (04:461–476). -/
theorem opus_corr_boxPhi_insert (T : (ι → ℕ) → ℝ) (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ)
    (E : Finset ι) (R : ι) (hR : R ∉ E) (u : ι → Fin 2 → ℕ) :
    opus_corr_boxPhi T A Wt (insert R E) u =
      opus_corr_boxOmega Wt E R u * opus_corr_boxIn T A Wt E R u *
        opus_corr_boxIn T A Wt E R (opus_corr_swap u R) := by
  have hbrzero : ∀ ω ∈ opus_corr_br E, ω R = 0 := fun ω hω => opus_corr_mem_br.mp hω R hR
  -- target and active rows
  have htarget : ∏ ω ∈ opus_corr_br (insert R E), T (opus_corr_ev u ω) =
      (∏ ω ∈ opus_corr_br E, T (opus_corr_ev u ω)) *
        ∏ ω ∈ opus_corr_br E, T (opus_corr_ev (opus_corr_swap u R) ω) := by
    rw [opus_corr_br_insert, opus_corr_supp_prod_insert _ R hR]
    congr 1
    apply Finset.prod_congr rfl
    intro ω hω
    rw [opus_corr_ev_update u R ω (hbrzero ω hω)]
  have hactive : ∏ ω ∈ opus_corr_br (insert R E),
        ∏ I ∈ Finset.univ.filter (fun I => I ∉ insert R E),
          A I (opus_corr_evI u (opus_corr_restr ω I)) =
      (∏ ω ∈ opus_corr_br E, ∏ I ∈ Finset.univ.filter (fun I => I ∉ insert R E),
          A I (opus_corr_evI u (opus_corr_restr ω I))) *
        ∏ ω ∈ opus_corr_br E, ∏ I ∈ Finset.univ.filter (fun I => I ∉ insert R E),
          A I (opus_corr_evI (opus_corr_swap u R) (opus_corr_restr ω I)) := by
    rw [opus_corr_br_insert, opus_corr_supp_prod_insert _ R hR]
    congr 1
    apply Finset.prod_congr rfl
    intro ω hω
    apply Finset.prod_congr rfl
    intro I hI
    have hRI : R ≠ I := by
      intro h; subst h; simp at hI
    rw [opus_corr_evI_restr_update u R I hRI ω (hbrzero ω hω)]
  -- weights
  have hweightsE : ∀ I ∈ E, ∏ η ∈ opus_corr_brI (insert R E) I, Wt I (opus_corr_evI u η) =
      (∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI u η)) *
        ∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI (opus_corr_swap u R) η) := by
    intro I hI
    have hRI : R ≠ I := fun h => hR (h ▸ hI)
    have hc : ¬ ((⟨R, hRI⟩ : {R // R ≠ I}).1 ∈ E) := hR
    rw [opus_corr_brI_insert_other E R I hRI,
      opus_corr_supp_prod_insert (fun x : {R // R ≠ I} => x.1 ∈ E) ⟨R, hRI⟩ hc]
    congr 1
    apply Finset.prod_congr rfl
    intro η hη
    have hη0 : η ⟨R, hRI⟩ = 0 := opus_corr_mem_brI.mp hη ⟨R, hRI⟩ hR
    rw [opus_corr_evI_update u R I hRI η hη0]
  have hweights : ∏ I ∈ insert R E, ∏ η ∈ opus_corr_brI (insert R E) I,
        Wt I (opus_corr_evI u η) =
      opus_corr_boxOmega Wt E R u *
        ((∏ I ∈ E, ∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI u η)) *
          ∏ I ∈ E, ∏ η ∈ opus_corr_brI E I, Wt I (opus_corr_evI (opus_corr_swap u R) η)) := by
    rw [Finset.prod_insert hR, opus_corr_brI_insert_self, ← Finset.prod_mul_distrib]
    unfold opus_corr_boxOmega
    congr 1
    exact Finset.prod_congr rfl hweightsE
  unfold opus_corr_boxPhi opus_corr_boxIn
  have hfilter : Finset.univ.filter (fun I => I ∉ insert R E) =
      Finset.univ.filter (fun I => I ∉ insert R (insert R E)) := by
    simp
  rw [htarget, hactive, hweights]
  ring

/-- `H_out` and `Ω_R` do not depend on the shifts of direction `R`. -/
theorem opus_corr_boxOut_setc (A : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ) (E : Finset ι)
    (R : ι) (u : ι → Fin 2 → ℕ) (b : Fin 2) (t : ℕ) :
    opus_corr_boxOut A E R (opus_corr_setc u R b t) = opus_corr_boxOut A E R u := by
  unfold opus_corr_boxOut
  apply Finset.prod_congr rfl
  intro ω _
  congr 1
  funext x
  have hx : x.1 ≠ R := x.2
  simp [opus_corr_evI, opus_corr_setc, Function.update_of_ne hx]

theorem opus_corr_boxOmega_setc (Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ) (E : Finset ι)
    (R : ι) (u : ι → Fin 2 → ℕ) (b : Fin 2) (t : ℕ) :
    opus_corr_boxOmega Wt E R (opus_corr_setc u R b t) = opus_corr_boxOmega Wt E R u := by
  unfold opus_corr_boxOmega
  apply Finset.prod_congr rfl
  intro η _
  congr 1
  funext x
  have hx : x.1 ≠ R := x.2
  simp [opus_corr_evI, opus_corr_setc, Function.update_of_ne hx]

/-- `H_in` does not depend on `u_R^1` when `R ∉ E`. -/
theorem opus_corr_boxIn_setc_one (T : (ι → ℕ) → ℝ) (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ)
    (E : Finset ι) (R : ι) (hR : R ∉ E) (u : ι → Fin 2 → ℕ) (t : ℕ) :
    opus_corr_boxIn T A Wt E R (opus_corr_setc u R 1 t) = opus_corr_boxIn T A Wt E R u := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hset : ∀ x (b : Fin 2), b ≠ 1 → opus_corr_setc u R 1 t x b = u x b := by
    intro x b hb
    unfold opus_corr_setc
    by_cases hx : x = R
    · subst x; simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hx]
  unfold opus_corr_boxIn
  congr 1
  congr 1
  · apply Finset.prod_congr rfl
    intro ω hω
    congr 1
    funext x
    unfold opus_corr_ev
    by_cases hx : x = R
    · subst x
      rw [opus_corr_mem_br.mp hω _ hR]
      exact hset _ 0 (by decide)
    · simp [opus_corr_setc, Function.update_of_ne hx]
  · apply Finset.prod_congr rfl
    intro ω hω
    apply Finset.prod_congr rfl
    intro I _
    congr 1
    funext x
    unfold opus_corr_evI opus_corr_restr
    by_cases hx : x.1 = R
    · rw [hx, opus_corr_mem_br.mp hω _ hR]
      exact hset _ 0 (by decide)
    · simp [opus_corr_setc, Function.update_of_ne hx]
  · apply Finset.prod_congr rfl
    intro I hI
    apply Finset.prod_congr rfl
    intro η hη
    congr 1
    funext x
    unfold opus_corr_evI
    by_cases hx : x.1 = R
    · have hη0 := opus_corr_mem_brI.mp hη x (by rw [hx]; exact hR)
      rw [hη0, hx]
      exact hset _ 0 (by decide)
    · simp [opus_corr_setc, Function.update_of_ne hx]

/-- `|H_out| ≤ Ω_R` from `|A_R| ≤ W_R`. -/
theorem opus_corr_boxOut_abs_le (A Wt : ∀ I : ι, ({R // R ≠ I} → ℕ) → ℝ) (E : Finset ι)
    (R : ι) (hR : R ∉ E) (hA : ∀ y, |A R y| ≤ Wt R y) (u : ι → Fin 2 → ℕ) :
    |opus_corr_boxOut A E R u| ≤ opus_corr_boxOmega Wt E R u := by
  unfold opus_corr_boxOut opus_corr_boxOmega
  rw [Finset.abs_prod]
  calc
    ∏ ω ∈ opus_corr_br E, |A R (opus_corr_evI u (opus_corr_restr ω R))| ≤
        ∏ ω ∈ opus_corr_br E, Wt R (opus_corr_evI u (opus_corr_restr ω R)) :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun ω _ => hA _)
    _ = ∏ η ∈ opus_corr_brI E R, Wt R (opus_corr_evI u η) := by
      apply Finset.prod_nbij' (fun ω => opus_corr_restr ω R)
        (fun η x => if hx : x = R then 0 else η ⟨x, hx⟩)
      · intro ω hω
        rw [opus_corr_mem_brI]
        intro x hx
        exact opus_corr_mem_br.mp hω x.1 hx
      · intro η hη
        rw [opus_corr_mem_br]
        intro x hx
        by_cases hxR : x = R
        · simp [hxR]
        · simp only [hxR, dite_false]
          exact opus_corr_mem_brI.mp hη ⟨x, hxR⟩ hx
      · intro ω hω
        funext x
        by_cases hxR : x = R
        · subst x; simp [opus_corr_mem_br.mp hω _ hR]
        · simp [hxR, opus_corr_restr]
      · intro η _
        funext x
        have hx : x.1 ≠ R := x.2
        simp [opus_corr_restr, hx]
      · intro ω _
        rfl

end BoxPhi

end
end HindmanSumsProducts
