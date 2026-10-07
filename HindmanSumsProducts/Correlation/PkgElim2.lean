import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for weighted additive elimination (04:418–572). -/

namespace HindmanSumsProducts
open FromArithmetic
open Filter
open scoped Topology

theorem c_elim2_weighted_variance_identity (b h c : ℝ) :
    b * h ^ 2 - (2 * c) * (b * h) + c ^ 2 * b = b * (h - c) ^ 2 := by
  ring

theorem c_elim2_weighted_variance_tendsto {B c : ℝ} (b h : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 B))
    (hbh : Tendsto (fun n => b n * h n) atTop (𝓝 (B * c)))
    (hbh2 : Tendsto (fun n => b n * h n ^ 2) atTop (𝓝 (B * c ^ 2))) :
    Tendsto (fun n => b n * (h n - c) ^ 2) atTop (𝓝 0) := by
  have hlinear : Tendsto
      (fun n => b n * h n ^ 2 - (2 * c) * (b n * h n) + c ^ 2 * b n)
      atTop (𝓝 (B * c ^ 2 - (2 * c) * (B * c) + c ^ 2 * B)) := by
    exact (hbh2.sub (hbh.const_mul (2 * c))).add (hb.const_mul (c ^ 2))
  have hzero : B * c ^ 2 - (2 * c) * (B * c) + c ^ 2 * B = 0 := by ring
  have heq : (fun n => b n * (h n - c) ^ 2) =ᶠ[atTop]
      fun n => b n * h n ^ 2 - (2 * c) * (b n * h n) + c ^ 2 * b n := by
    filter_upwards [] with n
    exact (c_elim2_weighted_variance_identity (b n) (h n) c).symm
  rw [hzero] at hlinear
  exact (tendsto_congr' heq).2 hlinear

theorem c_elim2_rowForm_add {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (p : Fin q → ℕ) (x y : Fin m → ℚ) (a : ℚ) :
    rowForm c T p (fun k => x k + a * y k) =
      rowForm c T p x + a * rowForm c T p y := by
  classical
  let w : Fin m → ℚ := fun k => c k / c T.anchor * T.value p k
  change (∑ k, w k * (x k + a * y k)) =
    (∑ k, w k * x k) + a * (∑ k, w k * y k)
  calc
    _ = (∑ k, w k * x k) + ∑ k, a * (w k * y k) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k, w k * x k) + a * (∑ k, w k * y k) := by
      rw [← Finset.mul_sum]
    _ = _ := by simp [w]

theorem c_elim2_targetVertex_add {m q r : ℕ} (c : Fin m → ℚ)
    (Sh : RowShape m q r) (p : Fin q → ℕ) (Mp : ℕ)
    (z v : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ)
    (ω : NonTarget Sh → Fin 2) (a : ℚ) :
    targetVertex c Sh p Mp (fun k => z k + a * v k) u ω =
      targetVertex c Sh p Mp z u ω +
        a * rowForm c (Sh.row Sh.star) p v := by
  simp [targetVertex, c_elim2_rowForm_add]
  ring

theorem c_elim2_atQ_add_int (g : ℤ → ℝ) (x : ℚ) (h : ℤ) :
    atQ g (x + h) = if x.den = 1 then g (x.num + h) else 0 := by
  by_cases hx : x.den = 1
  · have hx' : x = (x.num : ℤ) := (Rat.coe_int_num_of_den_eq_one hx).symm
    have hsum : x + h = ((x.num + h : ℤ) : ℚ) := by
      rw [hx']
      push_cast
      rfl
    have hden : (x + h).den = 1 := by simp [hx]
    have hnumCast : ((x + h).num : ℚ) = ((x.num + h : ℤ) : ℚ) := by
      rw [Rat.coe_int_num_of_den_eq_one hden, hsum]
    have hnum : (x + h).num = x.num + h := by exact_mod_cast hnumCast
    simp [atQ, hx, hnum]
  · simp [atQ, hx]

noncomputable def c_elim2_uniformIntervalAverage (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ n ∈ Finset.range L, f n

noncomputable def c_elim2_uniformIntervalPairAverage (L : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((L : ℝ) ^ 2)⁻¹ *
    ∑ x ∈ Finset.range L, ∑ y ∈ Finset.range L, f x * f y

theorem c_elim2_uniformIntervalAverage_ge_one {L : ℕ} (hL : 0 < L)
    (f : ℕ → ℝ) (hf : ∀ x ∈ Finset.range L, 1 ≤ f x) :
    1 ≤ c_elim2_uniformIntervalAverage L f := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hsum : (L : ℝ) ≤ ∑ x ∈ Finset.range L, f x := by
    calc
      (L : ℝ) = ∑ x ∈ Finset.range L, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ Finset.range L, f x :=
        Finset.sum_le_sum fun x hx => hf x hx
  unfold c_elim2_uniformIntervalAverage
  calc
    1 = (L : ℝ)⁻¹ * (L : ℝ) := by field_simp
    _ ≤ (L : ℝ)⁻¹ * ∑ x ∈ Finset.range L, f x :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLR.le)

theorem c_elim2_uniformIntervalPairAverage_eq_sq {L : ℕ} (f : ℕ → ℝ) :
    c_elim2_uniformIntervalPairAverage L f =
      (c_elim2_uniformIntervalAverage L f) ^ 2 := by
  unfold c_elim2_uniformIntervalPairAverage c_elim2_uniformIntervalAverage
  rw [← Finset.sum_mul_sum]
  ring

theorem c_elim2_uniformIntervalAverage_le_pair {L : ℕ} (hL : 0 < L)
    (f : ℕ → ℝ) (hf : ∀ x ∈ Finset.range L, 1 ≤ f x) :
    c_elim2_uniformIntervalAverage L f ≤ c_elim2_uniformIntervalPairAverage L f := by
  rw [c_elim2_uniformIntervalPairAverage_eq_sq]
  have h := c_elim2_uniformIntervalAverage_ge_one hL f hf
  nlinarith [sq_nonneg (c_elim2_uniformIntervalAverage L f - 1)]

universe u

abbrev c_elim2_ShiftCoord {α : Type u} (E : Finset α) :=
  {x : α × Fin 2 // x.2.val = 0 ∨ x.1 ∈ E}

abbrev c_elim2_ShiftCoordExcept {α : Type u} (E : Finset α) (R : α) :=
  {x : c_elim2_ShiftCoord E // x.val ≠ (R, 0)}

noncomputable def c_elim2_uniformFintypeAverage {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

theorem c_elim2_uniformFintypeAverage_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    c_elim2_uniformFintypeAverage f =
      c_elim2_uniformFintypeAverage (fun x =>
        c_elim2_uniformFintypeAverage (fun y => f (x, y))) := by
  classical
  unfold c_elim2_uniformFintypeAverage
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

theorem c_elim2_uniformFintypeAverage_sq {α : Type*} [Fintype α]
    (f : α → ℝ) :
    (c_elim2_uniformFintypeAverage f) ^ 2 =
      c_elim2_uniformFintypeAverage (fun p : α × α => f p.1 * f p.2) := by
  classical
  unfold c_elim2_uniformFintypeAverage
  rw [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Fintype.sum_mul_sum, mul_inv_rev]
  ring

theorem c_elim2_uniformFintypeAverage_const {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) : c_elim2_uniformFintypeAverage (fun _ : α => c) = c := by
  classical
  unfold c_elim2_uniformFintypeAverage
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := α))
  have hsum : (∑ x : α, c) = (Fintype.card α : ℝ) * c := by simp
  rw [hsum]
  field_simp

theorem c_elim2_uniformFintypeAverage_const_mul {α : Type*} [Fintype α]
    (c : ℝ) (f : α → ℝ) :
    c_elim2_uniformFintypeAverage (fun x => c * f x) =
      c * c_elim2_uniformFintypeAverage f := by
  classical
  unfold c_elim2_uniformFintypeAverage
  rw [← Finset.mul_sum]
  ring

noncomputable def c_elim2_shiftStateAverage {α : Type*} [Fintype α]
    [DecidableEq α] (E : Finset α) (L : ℕ)
    (F : (c_elim2_ShiftCoord E → Fin L) → ℝ) : ℝ := by
  classical
  exact c_elim2_uniformFintypeAverage F

noncomputable def c_elim2_shiftCoord_insert_equiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) (hR : R ∉ E) :
    c_elim2_ShiftCoord (insert R E) ≃ c_elim2_ShiftCoord E ⊕ PUnit.{u + 1} := by
  classical
  let extra : c_elim2_ShiftCoord (insert R E) :=
    ⟨(R, 1), Or.inr (Finset.mem_insert_self R E)⟩
  have hcoord (x : c_elim2_ShiftCoord (insert R E))
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
  let f : c_elim2_ShiftCoord (insert R E) → c_elim2_ShiftCoord E ⊕ PUnit :=
    fun x => if hx : x.val.1 = R ∧ x.val.2.val = 1 then Sum.inr PUnit.unit
      else Sum.inl ⟨x.val, hcoord x hx⟩
  let g : c_elim2_ShiftCoord E ⊕ PUnit → c_elim2_ShiftCoord (insert R E) :=
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

noncomputable def c_elim2_shiftCoord_split_equiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) :
    c_elim2_ShiftCoord E ≃ c_elim2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} := by
  classical
  let point : c_elim2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
  let f : c_elim2_ShiftCoord E → c_elim2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} :=
    fun x => if hx : x.val = (R, 0) then Sum.inr PUnit.unit else
      Sum.inl ⟨x, hx⟩
  let g : c_elim2_ShiftCoordExcept E R ⊕ PUnit.{u + 1} → c_elim2_ShiftCoord E :=
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

noncomputable def c_elim2_shiftCoordAssignmentSplitEquiv {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (L : ℕ) :
    (c_elim2_ShiftCoord E → Fin L) ≃
      (c_elim2_ShiftCoordExcept E R → Fin L) × Fin L := by
  classical
  let point : c_elim2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
  let f : (c_elim2_ShiftCoord E → Fin L) →
      (c_elim2_ShiftCoordExcept E R → Fin L) × Fin L :=
    fun u => (fun c => u c.val, u point)
  let g : (c_elim2_ShiftCoordExcept E R → Fin L) × Fin L →
      c_elim2_ShiftCoord E → Fin L := fun p c =>
    if h : c.val = (R, 0) then p.2 else p.1 ⟨c, h⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro u
    funext c
    by_cases h : c.val = (R, 0)
    · have hc : c = point := Subtype.ext h
      subst c
      simp [f, g, point]
    · simp [f, g, h]
  · intro p
    apply Prod.ext
    · funext c
      simp [f, g, c.property]
    · simp [f, g, point]

@[simp] theorem c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (L : ℕ)
    (o : c_elim2_ShiftCoordExcept E R → Fin L) (t : Fin L)
    (c : c_elim2_ShiftCoordExcept E R) :
    (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t) c.val = o c := by
  change (if h : c.val.val = (R, 0) then t else o ⟨c.val, h⟩) = o c
  simp [c.property]

@[simp] theorem c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_point
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (L : ℕ)
    (o : c_elim2_ShiftCoordExcept E R → Fin L) (t : Fin L) :
    (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t)
      ⟨(R, 0), Or.inl rfl⟩ = t := by
  change (if h : (R, 0) = (R, 0) then t else
    o ⟨⟨(R, 0), Or.inl rfl⟩, h⟩) = t
  simp

theorem c_elim2_shiftStateAverage_split {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (L : ℕ)
    (F : (c_elim2_ShiftCoord E → Fin L) → ℝ) :
    c_elim2_shiftStateAverage E L F =
      c_elim2_uniformFintypeAverage (fun v : c_elim2_ShiftCoordExcept E R → Fin L =>
        c_elim2_uniformFintypeAverage (fun t : Fin L =>
          F ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (v, t)))) := by
  classical
  let e := c_elim2_shiftCoordAssignmentSplitEquiv E R L
  have hsum : (∑ x : c_elim2_ShiftCoord E → Fin L, F x) =
      ∑ p : (c_elim2_ShiftCoordExcept E R → Fin L) × Fin L, F (e.symm p) := by
    exact Fintype.sum_equiv e F (fun p => F (e.symm p)) (by intro x; simp)
  have hcard : Fintype.card (c_elim2_ShiftCoord E → Fin L) =
      Fintype.card ((c_elim2_ShiftCoordExcept E R → Fin L) × Fin L) :=
    Fintype.card_congr e
  unfold c_elim2_shiftStateAverage c_elim2_uniformFintypeAverage
  rw [hsum, hcard]
  exact c_elim2_uniformFintypeAverage_prod (fun p => F (e.symm p))

noncomputable def c_elim2_shiftCoordExcept_insert_equiv {α : Type u}
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) :
    c_elim2_ShiftCoordExcept (insert R E) R ≃ c_elim2_ShiftCoord E := by
  classical
  let oldPoint : c_elim2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
  have hcoord (x : c_elim2_ShiftCoordExcept (insert R E) R)
      (hx : x.val.val.1 ≠ R) :
      x.val.val.2.val = 0 ∨ x.val.val.1 ∈ E := by
    rcases x.val.property with hzero | hxmem
    · exact Or.inl hzero
    · rcases Finset.mem_insert.mp hxmem with heq | hxE
      · exact False.elim (hx heq)
      · exact Or.inr hxE
  let f : c_elim2_ShiftCoordExcept (insert R E) R → c_elim2_ShiftCoord E :=
    fun x => if hx : x.val.val.1 = R then oldPoint else ⟨x.val.val, hcoord x hx⟩
  let g : c_elim2_ShiftCoord E → c_elim2_ShiftCoordExcept (insert R E) R :=
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

noncomputable def c_elim2_shiftStateInsertEquiv {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ) :
    (c_elim2_ShiftCoord (insert R E) → Fin L) ≃
      (c_elim2_ShiftCoord E → Fin L) × Fin L := by
  classical
  let eCoord := c_elim2_shiftCoord_insert_equiv E R hR
  exact (Equiv.arrowCongr eCoord (Equiv.refl (Fin L))).trans
    ((Equiv.sumArrowEquivProdArrow (c_elim2_ShiftCoord E) PUnit.{u + 1} (Fin L)).trans
      (Equiv.prodCongr (Equiv.refl (c_elim2_ShiftCoord E → Fin L))
        (Equiv.punitArrowEquiv (Fin L))) )

def c_elim2_shiftCoordInsertOld {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) (c : c_elim2_ShiftCoord E) :
    c_elim2_ShiftCoord (insert R E) :=
  ⟨c.val, Or.elim c.property Or.inl (fun hc => Or.inr (Finset.mem_insert_of_mem hc))⟩

def c_elim2_shiftCoordInsertExtra {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) :
    c_elim2_ShiftCoord (insert R E) :=
  ⟨(R, 1), Or.inr (Finset.mem_insert_self R E)⟩

@[simp] theorem c_elim2_shiftStateInsertEquiv_symm_apply_old {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (u : c_elim2_ShiftCoord E → Fin L) (t : Fin L) (c : c_elim2_ShiftCoord E) :
    (c_elim2_shiftStateInsertEquiv E R hR L).symm (u, t)
      (c_elim2_shiftCoordInsertOld E R c) = u c := by
  let e := c_elim2_shiftCoord_insert_equiv E R hR
  have hInv : e.symm (Sum.inl c) = c_elim2_shiftCoordInsertOld E R c := by
    apply Subtype.ext
    rfl
  have hc : e (c_elim2_shiftCoordInsertOld E R c) = Sum.inl c := by
    rw [← hInv]
    exact e.apply_symm_apply (Sum.inl c)
  change ((Equiv.sumArrowEquivProdArrow (c_elim2_ShiftCoord E)
      PUnit.{u + 1} (Fin L)).symm (u, (Equiv.punitArrowEquiv (Fin L)).symm t))
      (e (c_elim2_shiftCoordInsertOld E R c)) = u c
  rw [hc, Equiv.sumArrowEquivProdArrow_symm_apply_inl]

@[simp] theorem c_elim2_shiftStateInsertEquiv_symm_apply_extra {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (u : c_elim2_ShiftCoord E → Fin L) (t : Fin L) :
    (c_elim2_shiftStateInsertEquiv E R hR L).symm (u, t)
      (c_elim2_shiftCoordInsertExtra E R) = t := by
  let e := c_elim2_shiftCoord_insert_equiv E R hR
  have hInv : e.symm (Sum.inr PUnit.unit) = c_elim2_shiftCoordInsertExtra E R := by
    apply Subtype.ext
    rfl
  have hc : e (c_elim2_shiftCoordInsertExtra E R) = Sum.inr PUnit.unit := by
    rw [← hInv]
    exact e.apply_symm_apply (Sum.inr PUnit.unit)
  change ((Equiv.sumArrowEquivProdArrow (c_elim2_ShiftCoord E)
      PUnit.{u + 1} (Fin L)).symm (u, (Equiv.punitArrowEquiv (Fin L)).symm t))
      (e (c_elim2_shiftCoordInsertExtra E R)) = t
  rw [hc, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  simp [Equiv.punitArrowEquiv]

theorem c_elim2_shiftStateAverage_insert {α : Type*} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (F : (c_elim2_ShiftCoord (insert R E) → Fin L) → ℝ) :
    c_elim2_shiftStateAverage (insert R E) L F =
      c_elim2_shiftStateAverage E L (fun u =>
        c_elim2_uniformFintypeAverage (fun t : Fin L =>
          F ((c_elim2_shiftStateInsertEquiv E R hR L).symm (u, t)))) := by
  classical
  let e := c_elim2_shiftStateInsertEquiv E R hR L
  have hsum : (∑ u : c_elim2_ShiftCoord (insert R E) → Fin L, F u) =
      ∑ p : (c_elim2_ShiftCoord E → Fin L) × Fin L, F (e.symm p) := by
    exact Fintype.sum_equiv e F (fun p => F (e.symm p)) (by intro u; simp)
  have hcard : Fintype.card (c_elim2_ShiftCoord (insert R E) → Fin L) =
      Fintype.card ((c_elim2_ShiftCoord E → Fin L) × Fin L) :=
    Fintype.card_congr e
  unfold c_elim2_shiftStateAverage c_elim2_uniformFintypeAverage
  rw [hsum, hcard]
  exact c_elim2_uniformFintypeAverage_prod (fun p => F (e.symm p))

abbrev c_elim2_ShiftOutside {α : Type u} (E : Finset α) (R : α) (L : ℕ) :=
  c_elim2_ShiftCoordExcept E R → Fin L

noncomputable def c_elim2_jointStateAverage {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (μ : β → ℝ)
    (L : β → ℕ) (F : ∀ b, (c_elim2_ShiftCoord E → Fin (L b)) → ℝ) : ℝ :=
  ∑ b, μ b * c_elim2_shiftStateAverage E (L b) (F b)

theorem c_elim2_sigma_weighted_uniform_sum {β : Type*} [Fintype β]
    (O : β → Type*) [∀ b, Fintype (O b)] (μ : β → ℝ)
    (F : ∀ b, O b → ℝ) :
    ∑' x : Σ b, O b,
        μ x.1 * (Fintype.card (O x.1) : ℝ)⁻¹ * F x.1 x.2 =
      ∑ b, μ b * c_elim2_uniformFintypeAverage (F b) := by
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
  unfold c_elim2_uniformFintypeAverage
  rfl

noncomputable def c_elim2_csCurrentIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (L : β → ℕ)
    (H₀ : ∀ b, c_elim2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, c_elim2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (b : β) (u : c_elim2_ShiftCoord E → Fin (L b)) : ℝ :=
  let e := c_elim2_shiftCoordAssignmentSplitEquiv E R (L b)
  H₀ b (e u).1 * c_elim2_uniformFintypeAverage (H b (e u).1)

noncomputable def c_elim2_csWeightIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (L : β → ℕ)
    (Ω : ∀ b, c_elim2_ShiftOutside E R (L b) → ℝ)
    (b : β) (u : c_elim2_ShiftCoord E → Fin (L b)) : ℝ :=
  Ω b ((c_elim2_shiftCoordAssignmentSplitEquiv E R (L b) u).1)

noncomputable def c_elim2_csNextIntegrand {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (hR : R ∉ E)
    (L : β → ℕ) (Ω : ∀ b, c_elim2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, c_elim2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (b : β) (u : c_elim2_ShiftCoord (insert R E) → Fin (L b)) : ℝ := by
  classical
  let (v, t₁) := c_elim2_shiftStateInsertEquiv E R hR (L b) u
  let (o, t₀) := c_elim2_shiftCoordAssignmentSplitEquiv E R (L b) v
  exact Ω b o * H b o t₀ * H b o t₁

theorem c_elim2_weightedShiftStateStep {α β : Type u} [Fintype α]
    [DecidableEq α] [Fintype β] (E : Finset α) (R : α) (hR : R ∉ E)
    (μ : β → ℝ) (L : β → ℕ) (hL : ∀ b, 0 < L b)
    (H₀ : ∀ b, c_elim2_ShiftOutside E R (L b) → ℝ)
    (Ω : ∀ b, c_elim2_ShiftOutside E R (L b) → ℝ)
    (H : ∀ b, c_elim2_ShiftOutside E R (L b) → Fin (L b) → ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hΩ : ∀ b o, 0 ≤ Ω b o)
    (h₀ : ∀ b o, |H₀ b o| ≤ Ω b o)
    (hCS : ∀ {γ : Type u} (μ Ω H₀ H₁ : γ → ℝ)
      (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
      (h₀ : ∀ x, |H₀ x| ≤ Ω x)
      (hΩs : Summable (fun x => μ x * Ω x))
      (h₁s : Summable (fun x => μ x * (Ω x * H₁ x ^ 2))),
      |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
        (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2)) :
    |c_elim2_jointStateAverage E μ L
        (c_elim2_csCurrentIntegrand E R L H₀ H)| ^ 2 ≤
      c_elim2_jointStateAverage E μ L (c_elim2_csWeightIntegrand E R L Ω) *
        c_elim2_jointStateAverage (insert R E) μ L
          (c_elim2_csNextIntegrand E R hR L Ω H) := by
  classical
  let Outside : β → Type _ := fun b => c_elim2_ShiftOutside (α := α) E R (L b)
  let γ := Σ b, Outside b
  letI : ∀ b, Fintype (Outside b) := fun b => by
    dsimp [Outside, c_elim2_ShiftOutside]
    infer_instance
  letI : Fintype γ := by
    dsimp [γ]
    infer_instance
  let μ' : γ → ℝ := fun x => μ x.1 * (Fintype.card (Outside x.1) : ℝ)⁻¹
  let Ω' : γ → ℝ := fun x => Ω x.1 x.2
  let H₀' : γ → ℝ := fun x => H₀ x.1 x.2
  let H₁' : γ → ℝ := fun x =>
    c_elim2_uniformFintypeAverage (H x.1 x.2)
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
      c_elim2_shiftStateAverage E (L b)
        (c_elim2_csCurrentIntegrand E R L H₀ H b) =
      c_elim2_uniformFintypeAverage (fun o : Outside b =>
        H₀ b o * c_elim2_uniformFintypeAverage (H b o)) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    rw [c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    simp only [c_elim2_csCurrentIntegrand, Equiv.apply_symm_apply]
    apply congrArg (fun f : Outside b → ℝ => c_elim2_uniformFintypeAverage f)
    funext o
    exact c_elim2_uniformFintypeAverage_const
      (H₀ b o * c_elim2_uniformFintypeAverage (H b o))
  have hweight (b : β) :
      c_elim2_shiftStateAverage E (L b)
        (c_elim2_csWeightIntegrand E R L Ω b) =
      c_elim2_uniformFintypeAverage (Ω b) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    rw [c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    simp only [c_elim2_csWeightIntegrand, Equiv.apply_symm_apply]
    apply congrArg (fun f : Outside b → ℝ => c_elim2_uniformFintypeAverage f)
    funext o
    exact c_elim2_uniformFintypeAverage_const (Ω b o)
  have hnext (b : β) :
      c_elim2_shiftStateAverage (insert R E) (L b)
        (c_elim2_csNextIntegrand E R hR L Ω H b) =
      c_elim2_uniformFintypeAverage (fun o : Outside b =>
        c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          c_elim2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
            Ω b o * H b o t₀ * H b o t₁))) := by
    letI : Nonempty (Fin (L b)) := ⟨⟨0, hL b⟩⟩
    let eIns := c_elim2_shiftStateInsertEquiv E R hR (L b)
    let eSplit := c_elim2_shiftCoordAssignmentSplitEquiv E R (L b)
    have hEval (o : Outside b) (t₀ t₁ : Fin (L b)) :
        c_elim2_csNextIntegrand E R hR L Ω H b
          ((c_elim2_shiftStateInsertEquiv E R hR (L b)).symm
            ((c_elim2_shiftCoordAssignmentSplitEquiv E R (L b)).symm (o, t₀), t₁)) =
            Ω b o * H b o t₀ * H b o t₁ := by
      simp [c_elim2_csNextIntegrand]
    rw [c_elim2_shiftStateAverage_insert (E := E) (R := R) (hR := hR) (L := L b)]
    rw [c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L b)]
    change c_elim2_uniformFintypeAverage (fun o : Outside b =>
      c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
        c_elim2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
          c_elim2_csNextIntegrand E R hR L Ω H b
            (eIns.symm (eSplit.symm (o, t₀), t₁))))) = _
    apply congrArg (fun f : Outside b → ℝ => c_elim2_uniformFintypeAverage f)
    funext o
    apply congrArg (fun f : Fin (L b) → ℝ => c_elim2_uniformFintypeAverage f)
    funext t₀
    apply congrArg (fun f : Fin (L b) → ℝ => c_elim2_uniformFintypeAverage f)
    funext t₁
    exact hEval o t₀ t₁
  have hleft :
      (∑' x : γ, μ' x * (H₀' x * H₁' x)) =
        c_elim2_jointStateAverage E μ L
          (c_elim2_csCurrentIntegrand E R L H₀ H) := by
    have hsum := c_elim2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => H₀ b o * c_elim2_uniformFintypeAverage (H b o))
    have houter :
        (∑' x : γ, μ' x * (H₀' x * H₁' x)) =
          ∑ b, μ b * c_elim2_uniformFintypeAverage (fun o : Outside b =>
            H₀ b o * c_elim2_uniformFintypeAverage (H b o)) := by
      simpa [μ', H₀', H₁', Outside, mul_assoc] using hsum
    calc
      _ = ∑ b, μ b * c_elim2_uniformFintypeAverage (fun o : Outside b =>
            H₀ b o * c_elim2_uniformFintypeAverage (H b o)) := houter
      _ = _ := by
        unfold c_elim2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hcurrent b]
  have hfirst :
      (∑' x : γ, μ' x * Ω' x) =
        c_elim2_jointStateAverage E μ L (c_elim2_csWeightIntegrand E R L Ω) := by
    have hsum := c_elim2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => Ω b o)
    have houter : (∑' x : γ, μ' x * Ω' x) =
        ∑ b, μ b * c_elim2_uniformFintypeAverage (Ω b) := by
      simpa [μ', Ω', Outside] using hsum
    calc
      _ = ∑ b, μ b * c_elim2_uniformFintypeAverage (Ω b) := houter
      _ = _ := by
        unfold c_elim2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hweight b]
  have hpair (b : β) (o : Outside b) :
      c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
        c_elim2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
          Ω b o * H b o t₀ * H b o t₁)) =
    Ω b o * (c_elim2_uniformFintypeAverage (H b o)) ^ 2 := by
    calc
      _ = c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          (Ω b o * H b o t₀) * c_elim2_uniformFintypeAverage (H b o)) := by
        apply congrArg (fun f : Fin (L b) → ℝ => c_elim2_uniformFintypeAverage f)
        funext t₀
        simpa [mul_assoc] using
          (c_elim2_uniformFintypeAverage_const_mul
            (Ω b o * H b o t₀) (H b o))
      _ = c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
          (Ω b o * c_elim2_uniformFintypeAverage (H b o)) * H b o t₀) := by
        apply congrArg (fun f : Fin (L b) → ℝ => c_elim2_uniformFintypeAverage f)
        funext t₀
        ring
      _ = (Ω b o * c_elim2_uniformFintypeAverage (H b o)) *
          c_elim2_uniformFintypeAverage (H b o) :=
        c_elim2_uniformFintypeAverage_const_mul
          (Ω b o * c_elim2_uniformFintypeAverage (H b o)) (H b o)
      _ = _ := by ring
  have hnextReduce (b : β) :
      c_elim2_uniformFintypeAverage (fun o : Outside b =>
        Ω b o * (c_elim2_uniformFintypeAverage (H b o)) ^ 2) =
      c_elim2_shiftStateAverage (insert R E) (L b)
        (c_elim2_csNextIntegrand E R hR L Ω H b) := by
    calc
      _ = c_elim2_uniformFintypeAverage (fun o : Outside b =>
          c_elim2_uniformFintypeAverage (fun t₀ : Fin (L b) =>
            c_elim2_uniformFintypeAverage (fun t₁ : Fin (L b) =>
              Ω b o * H b o t₀ * H b o t₁))) := by
        congr 1
        funext o
        exact (hpair b o).symm
      _ = _ := (hnext b).symm
  have hsecond :
      (∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2)) =
        c_elim2_jointStateAverage (insert R E) μ L
          (c_elim2_csNextIntegrand E R hR L Ω H) := by
    have hsum := c_elim2_sigma_weighted_uniform_sum (O := Outside) μ
      (fun b o => Ω b o * (c_elim2_uniformFintypeAverage (H b o)) ^ 2)
    have houter :
        (∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2)) =
          ∑ b, μ b * c_elim2_uniformFintypeAverage (fun o : Outside b =>
            Ω b o * (c_elim2_uniformFintypeAverage (H b o)) ^ 2) := by
      simpa [μ', Ω', H₁', Outside, mul_assoc] using hsum
    calc
      _ = ∑ b, μ b * c_elim2_uniformFintypeAverage (fun o : Outside b =>
            Ω b o * (c_elim2_uniformFintypeAverage (H b o)) ^ 2) := houter
      _ = _ := by
        unfold c_elim2_jointStateAverage
        apply Finset.sum_congr rfl
        intro b hb
        rw [← hnextReduce b]
  calc
    |c_elim2_jointStateAverage E μ L
        (c_elim2_csCurrentIntegrand E R L H₀ H)| ^ 2 =
        |∑' x : γ, μ' x * (H₀' x * H₁' x)| ^ 2 := by rw [hleft]
    _ ≤ (∑' x : γ, μ' x * Ω' x) *
        ∑' x : γ, μ' x * (Ω' x * H₁' x ^ 2) := hcs
    _ = _ := by rw [hfirst, hsecond]

structure c_elim2_AdditiveBoxData (α β : Type u) [Fintype α] [DecidableEq α] where
  shiftLength : β → ℕ
  targetBase : β → ℚ
  targetCoefficient : β → α → ℤ
  targetFunction : β → ℚ → ℝ
  rowBase : α → β → ℚ
  rowCoefficient : α → α → β → ℤ
  rowFunction : α → β → ℚ → ℝ
  rowWeight : α → β → ℚ → ℝ

abbrev c_elim2_BoxBranch {α : Type u} (E : Finset α) :=
  {i : α // i ∈ E} → Fin 2

abbrev c_elim2_BoxRetainedBranch {α : Type u} [DecidableEq α]
    (E : Finset α) (I : α) :=
  c_elim2_BoxBranch (E.erase I)

def c_elim2_boxBranchFull {α : Type u} [DecidableEq α] (E : Finset α)
    (ω : c_elim2_BoxBranch E) : α → Fin 2 :=
  fun i => if hi : i ∈ E then ω ⟨i, hi⟩ else 0

def c_elim2_boxRetainedBranchFull {α : Type u} [DecidableEq α]
    (E : Finset α) (I : α) (η : c_elim2_BoxRetainedBranch E I) : α → Fin 2 :=
  c_elim2_boxBranchFull (E.erase I) η

def c_elim2_boxShiftValue {α : Type u} [DecidableEq α]
    (E : Finset α) {L : ℕ} (u : c_elim2_ShiftCoord E → Fin L)
    (ω : α → Fin 2) (i : α) : ℕ :=
  if hi : i ∈ E then (u ⟨(i, ω i), Or.inr hi⟩).val
  else (u ⟨(i, 0), Or.inl rfl⟩).val

def c_elim2_boxTargetArgument {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b))
    (ω : c_elim2_BoxBranch E) : ℚ :=
  D.targetBase b + ∑ i, (D.targetCoefficient b i : ℚ) *
    (c_elim2_boxShiftValue E u (c_elim2_boxBranchFull E ω) i : ℚ)

def c_elim2_boxRowArgument {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β) (I : α)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) (ω : α → Fin 2) : ℚ :=
  D.rowBase I b + ∑ i ∈ Finset.univ.erase I,
    (D.rowCoefficient I i b : ℚ) * (c_elim2_boxShiftValue E u ω i : ℚ)

def c_elim2_boxTargetProduct {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ ω : c_elim2_BoxBranch E,
    D.targetFunction b (c_elim2_boxTargetArgument D E b u ω)

def c_elim2_boxActiveProduct {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ I : {i : α // i ∉ E}, ∏ ω : c_elim2_BoxBranch E,
    D.rowFunction I.1 b
      (c_elim2_boxRowArgument D E b I.1 u (c_elim2_boxBranchFull E ω))

def c_elim2_boxRetainedProduct {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ I : {i : α // i ∈ E}, ∏ η : c_elim2_BoxRetainedBranch E I.1,
    D.rowWeight I.1 b
      (c_elim2_boxRowArgument D E b I.1 u
        (c_elim2_boxRetainedBranchFull E I.1 η))

def c_elim2_boxStateIntegrand {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  c_elim2_boxTargetProduct D E b u * c_elim2_boxActiveProduct D E b u *
    c_elim2_boxRetainedProduct D E b u

def c_elim2_boxActiveRowFactor {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ ω : c_elim2_BoxBranch E,
    D.rowFunction R b
      (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω))

def c_elim2_boxWeightRowFactor {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ ω : c_elim2_BoxBranch E,
      D.rowWeight R b
        (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω))

def c_elim2_boxOtherActiveProduct {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
  ∏ I : {i : α // i ∉ E ∧ i ≠ R}, ∏ ω : c_elim2_BoxBranch E,
    D.rowFunction I.1 b
      (c_elim2_boxRowArgument D E b I.1 u (c_elim2_boxBranchFull E ω))

def c_elim2_boxWithoutActiveRow {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ :=
    c_elim2_boxTargetProduct D E b u *
    c_elim2_boxOtherActiveProduct D E R b u *
    c_elim2_boxRetainedProduct D E b u

abbrev c_elim2_ActiveRowIndex {α : Type u} (E : Finset α) :=
  {i : α // i ∉ E}

abbrev c_elim2_ActiveRowIndexExcept {α : Type u} (E : Finset α) (R : α) :=
  {i : α // i ∉ E ∧ i ≠ R}

noncomputable def c_elim2_activeRowIndexEquiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) (hR : R ∉ E) :
    c_elim2_ActiveRowIndex E ≃ c_elim2_ActiveRowIndexExcept E R ⊕ PUnit.{u + 1} := by
  classical
  let f : c_elim2_ActiveRowIndex E →
      c_elim2_ActiveRowIndexExcept E R ⊕ PUnit.{u + 1} := fun x =>
    if hx : x.val = R then Sum.inr PUnit.unit
    else Sum.inl ⟨x.val, ⟨x.property, hx⟩⟩
  let g : c_elim2_ActiveRowIndexExcept E R ⊕ PUnit.{u + 1} →
      c_elim2_ActiveRowIndex E := fun y => match y with
    | Sum.inl x => ⟨x.val, x.property.1⟩
    | Sum.inr _ => ⟨R, hR⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    by_cases hx : x.val = R
    · have hEq : (⟨R, hR⟩ : c_elim2_ActiveRowIndex E) = x :=
        Subtype.ext hx.symm
      simpa [f, g, hx] using hEq
    · simp [f, g, hx]
  · intro y
    cases y with
    | inl x =>
        have hx : x.val ≠ R := x.property.2
        simp [f, g, hx]
    | inr y =>
        cases y
        simp [f, g]

theorem c_elim2_boxState_factor_active {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) :
    c_elim2_boxStateIntegrand D E b u =
      c_elim2_boxActiveRowFactor D E R b u * c_elim2_boxWithoutActiveRow D E R b u := by
  classical
  let e := c_elim2_activeRowIndexEquiv E R hR
  let rowProd : c_elim2_ActiveRowIndex E → ℝ := fun I =>
    ∏ ω : c_elim2_BoxBranch E,
      D.rowFunction I.1 b
        (c_elim2_boxRowArgument D E b I.1 u (c_elim2_boxBranchFull E ω))
  have hprod : (∏ I : c_elim2_ActiveRowIndex E, rowProd I) =
      ∏ J : c_elim2_ActiveRowIndexExcept E R ⊕ PUnit.{u + 1},
        rowProd (e.symm J) := by
    exact Fintype.prod_equiv e rowProd (fun J => rowProd (e.symm J))
      (by intro I; simp)
  have hsum :
      (∏ J : c_elim2_ActiveRowIndexExcept E R ⊕ PUnit.{u + 1},
        rowProd (e.symm J)) =
      (∏ I : c_elim2_ActiveRowIndexExcept E R, rowProd ⟨I.val, I.property.1⟩) *
        rowProd ⟨R, hR⟩ := by
    rw [Fintype.prod_sum_type]
    simp [e, c_elim2_activeRowIndexEquiv, rowProd]
  have hactive : c_elim2_boxActiveProduct D E b u =
      c_elim2_boxActiveRowFactor D E R b u *
        (∏ I : c_elim2_ActiveRowIndexExcept E R,
          rowProd ⟨I.val, I.property.1⟩) := by
    unfold c_elim2_boxActiveProduct c_elim2_boxActiveRowFactor
    change (∏ I : c_elim2_ActiveRowIndex E, rowProd I) =
      rowProd ⟨R, hR⟩ * (∏ I : c_elim2_ActiveRowIndexExcept E R,
        rowProd ⟨I.val, I.property.1⟩)
    rw [hprod, hsum]
    ring
  unfold c_elim2_boxStateIntegrand c_elim2_boxWithoutActiveRow
    c_elim2_boxOtherActiveProduct
  rw [hactive]
  ring

noncomputable def c_elim2_finsetSubtypeInsertEquiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) (hR : R ∉ E) :
    {i : α // i ∈ insert R E} ≃ {i : α // i ∈ E} ⊕ PUnit.{u + 1} := by
  classical
  let f : {i : α // i ∈ insert R E} → {i : α // i ∈ E} ⊕ PUnit.{u + 1} :=
    fun i => if hi : i.val = R then Sum.inr PUnit.unit else
      Sum.inl ⟨i.val, (Finset.mem_insert.mp i.property).resolve_left hi⟩
  let g : {i : α // i ∈ E} ⊕ PUnit.{u + 1} → {i : α // i ∈ insert R E} :=
    fun j => match j with
      | Sum.inl i => ⟨i.val, Finset.mem_insert_of_mem i.property⟩
      | Sum.inr _ => ⟨R, Finset.mem_insert_self R E⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro i
    by_cases hi : i.val = R
    · have heq : (⟨R, Finset.mem_insert_self R E⟩ : {i : α // i ∈ insert R E}) = i :=
        Subtype.ext hi.symm
      simpa [f, g, hi] using heq
    · simp [f, g, hi]
  · intro j
    cases j with
    | inl i =>
        have hi : i.val ≠ R := by
          intro heq
          exact hR (heq ▸ i.property)
        simp [f, g, hi]
    | inr j =>
        cases j
        simp [f, g]

noncomputable def c_elim2_boxBranchInsertEquiv {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) :
    c_elim2_BoxBranch (insert R E) ≃ c_elim2_BoxBranch E × Fin 2 := by
  classical
  let f : c_elim2_BoxBranch (insert R E) → c_elim2_BoxBranch E × Fin 2 :=
    fun ω => (fun i => ω ⟨i.val, Finset.mem_insert_of_mem i.property⟩,
      ω ⟨R, Finset.mem_insert_self R E⟩)
  let g : c_elim2_BoxBranch E × Fin 2 → c_elim2_BoxBranch (insert R E) :=
    fun p i => if hi : i.val = R then p.2 else
      p.1 ⟨i.val, (Finset.mem_insert.mp i.property).resolve_left hi⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro ω
    funext i
    by_cases hi : i.val = R
    · change (if h : i.val = R then ω ⟨R, Finset.mem_insert_self R E⟩ else
          ω ⟨i.val, Finset.mem_insert_of_mem
            ((Finset.mem_insert.mp i.property).resolve_left h)⟩) = ω i
      rw [dif_pos hi]
      have hEq : (⟨R, Finset.mem_insert_self R E⟩ : {i : α // i ∈ insert R E}) = i :=
        Subtype.ext hi.symm
      exact congrArg ω hEq
    · change (if h : i.val = R then ω ⟨R, Finset.mem_insert_self R E⟩ else
          ω ⟨i.val, Finset.mem_insert_of_mem
            ((Finset.mem_insert.mp i.property).resolve_left h)⟩) = ω i
      rw [dif_neg hi]
  · intro p
    apply Prod.ext
    · funext i
      have hi : i.val ≠ R := by
        intro heq
        exact hR (heq ▸ i.property)
      simp [f, g, hi]
    · simp [f, g]

@[simp] theorem c_elim2_boxBranchInsertEquiv_apply_old {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (ω : c_elim2_BoxBranch (insert R E)) (i : {i : α // i ∈ E}) :
    (c_elim2_boxBranchInsertEquiv E R hR ω).1 i =
      ω ⟨i.val, Finset.mem_insert_of_mem i.property⟩ := by
  rfl

@[simp] theorem c_elim2_boxBranchInsertEquiv_apply_new {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (ω : c_elim2_BoxBranch (insert R E)) :
    (c_elim2_boxBranchInsertEquiv E R hR ω).2 =
      ω ⟨R, Finset.mem_insert_self R E⟩ := by
  rfl

@[simp] theorem c_elim2_boxBranchInsertEquiv_symm_apply_old {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (ω : c_elim2_BoxBranch E) (b : Fin 2) (i : {i : α // i ∈ E}) :
    ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b))
        ⟨i.val, Finset.mem_insert_of_mem i.property⟩ = ω i := by
  have hne : i.val ≠ R := by
    intro heq
    exact hR (heq ▸ i.property)
  let e := c_elim2_boxBranchInsertEquiv E R hR
  have hproj := c_elim2_boxBranchInsertEquiv_apply_old E R hR (e.symm (ω, b)) i
  have hEq := congrArg (fun p : c_elim2_BoxBranch E × Fin 2 => p.1 i)
    (e.apply_symm_apply (ω, b))
  calc
    e.symm (ω, b) ⟨i.val, Finset.mem_insert_of_mem i.property⟩ =
        (e (e.symm (ω, b))).1 i := hproj.symm
    _ = ω i := hEq

@[simp] theorem c_elim2_boxBranchInsertEquiv_symm_apply_new {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (ω : c_elim2_BoxBranch E) (b : Fin 2) :
  ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b))
        ⟨R, Finset.mem_insert_self R E⟩ = b := by
  let e := c_elim2_boxBranchInsertEquiv E R hR
  have hproj := c_elim2_boxBranchInsertEquiv_apply_new E R hR (e.symm (ω, b))
  have hEq := congrArg Prod.snd (e.apply_symm_apply (ω, b))
  calc
    e.symm (ω, b) ⟨R, Finset.mem_insert_self R E⟩ =
        (e (e.symm (ω, b))).2 := hproj.symm
    _ = b := hEq



noncomputable def c_elim2_boxRetainedBranchInsertEquiv {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R I : α)
    (hR : R ∉ E) (hI : I ∈ E) :
    c_elim2_BoxRetainedBranch (insert R E) I ≃
      c_elim2_BoxRetainedBranch E I × Fin 2 := by
  classical
  have hRI : R ≠ I := by
    intro heq
    subst I
    exact hR hI
  have hSet : (insert R E).erase I = insert R (E.erase I) :=
    Finset.erase_insert_of_ne hRI
  have hR' : R ∉ E.erase I := by
    intro h
    exact hR (Finset.mem_erase.mp h).2
  let eDom : {i : α // i ∈ (insert R E).erase I} ≃
      {i : α // i ∈ insert R (E.erase I)} :=
    Equiv.subtypeEquivRight (fun i => by rw [hSet])
  exact (Equiv.arrowCongr eDom (Equiv.refl (Fin 2))).trans
    (c_elim2_boxBranchInsertEquiv (E.erase I) R hR')

@[simp] theorem c_elim2_boxRetainedBranchInsertEquiv_symm_apply_old
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (R I : α)
    (hR : R ∉ E) (hI : I ∈ E) (η : c_elim2_BoxRetainedBranch E I)
    (bit : Fin 2) (j : {j : α // j ∈ E.erase I}) :
    ((c_elim2_boxRetainedBranchInsertEquiv E R I hR hI).symm (η, bit))
      ⟨j.val, by
        have hRI : R ≠ I := by
          intro heq
          subst I
          exact hR hI
        rw [Finset.erase_insert_of_ne hRI]
        exact Finset.mem_insert_of_mem j.property⟩ = η j := by
  have hRI : R ≠ I := by
    intro heq
    subst I
    exact hR hI
  have hSet : (insert R E).erase I = insert R (E.erase I) :=
    Finset.erase_insert_of_ne hRI
  have hR' : R ∉ E.erase I := by
    intro h
    exact hR (Finset.mem_erase.mp h).2
  change ((c_elim2_boxBranchInsertEquiv (E.erase I) R hR').symm (η, bit))
    ⟨j.val, Finset.mem_insert_of_mem j.property⟩ = η j
  exact c_elim2_boxBranchInsertEquiv_symm_apply_old
    (E.erase I) R hR' η bit j

@[simp] theorem c_elim2_boxRetainedBranchInsertEquiv_symm_apply_new
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (R I : α)
    (hR : R ∉ E) (hI : I ∈ E) (η : c_elim2_BoxRetainedBranch E I)
    (bit : Fin 2) :
    ((c_elim2_boxRetainedBranchInsertEquiv E R I hR hI).symm (η, bit))
      ⟨R, by
        have hRI : R ≠ I := by
          intro heq
          subst I
          exact hR hI
        rw [Finset.erase_insert_of_ne hRI]
        exact Finset.mem_insert_self R (E.erase I)⟩ = bit := by
  have hRI : R ≠ I := by
    intro heq
    subst I
    exact hR hI
  have hSet : (insert R E).erase I = insert R (E.erase I) :=
    Finset.erase_insert_of_ne hRI
  have hR' : R ∉ E.erase I := by
    intro h
    exact hR (Finset.mem_erase.mp h).2
  change ((c_elim2_boxBranchInsertEquiv (E.erase I) R hR').symm (η, bit))
    ⟨R, Finset.mem_insert_self R (E.erase I)⟩ = bit
  exact c_elim2_boxBranchInsertEquiv_symm_apply_new
    (E.erase I) R hR' η bit

noncomputable def c_elim2_boxEndpointAssignment {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L) :
    c_elim2_ShiftCoord (insert R E) → Fin L :=
  (c_elim2_shiftStateInsertEquiv E R hR L).symm
    ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₀), t₁)

noncomputable def c_elim2_boxOldEndpointAssignment {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (L : ℕ)
    (o : c_elim2_ShiftOutside E R L) (t : Fin L) :
    c_elim2_ShiftCoord E → Fin L :=
  (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t)

@[simp] theorem c_elim2_boxEndpointAssignment_old_eval {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (L : ℕ) (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L)
    (c : c_elim2_ShiftCoord E) :
    c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
      (c_elim2_shiftCoordInsertOld E R c) =
    c_elim2_boxOldEndpointAssignment E R L o t₀ c := by
  simp only [c_elim2_boxEndpointAssignment,
    c_elim2_shiftStateInsertEquiv_symm_apply_old,
    c_elim2_boxOldEndpointAssignment]

@[simp] theorem c_elim2_boxEndpointAssignment_extra_eval {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E)
    (L : ℕ) (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L) :
    c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
      (c_elim2_shiftCoordInsertExtra E R) = t₁ := by
  simp only [c_elim2_boxEndpointAssignment,
    c_elim2_shiftStateInsertEquiv_symm_apply_extra]

def c_elim2_boxEndpointChoice {L : ℕ} (t₀ t₁ : Fin L) (b : Fin 2) : Fin L :=
  if b.val = 0 then t₀ else t₁

theorem c_elim2_boxShiftValue_endpoint {α : Type u} [Fintype α]
    [DecidableEq α] (E : Finset α) (R : α) (hR : R ∉ E) (L : ℕ)
    (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L)
    (ω : c_elim2_BoxBranch E) (b : Fin 2) (i : α) :
    c_elim2_boxShiftValue (insert R E)
      (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁)
      (c_elim2_boxBranchFull (insert R E)
        ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b))) i =
    c_elim2_boxShiftValue E
      (c_elim2_boxOldEndpointAssignment E R L o
        (c_elim2_boxEndpointChoice t₀ t₁ b))
      (c_elim2_boxBranchFull E ω) i := by
  classical
  have hbranchOld (j : α) (hj : j ∈ E) :
      c_elim2_boxBranchFull (insert R E)
          ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) j =
        c_elim2_boxBranchFull E ω j := by
    simpa [c_elim2_boxBranchFull, hj] using
      c_elim2_boxBranchInsertEquiv_symm_apply_old E R hR ω b ⟨j, hj⟩
  have hbranchNew :
      c_elim2_boxBranchFull (insert R E)
          ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R = b := by
    simpa [c_elim2_boxBranchFull] using
      c_elim2_boxBranchInsertEquiv_symm_apply_new E R hR ω b
  by_cases hiE : i ∈ E
  · have hiR : i ≠ R := by
      intro heq
      subst i
      exact hR hiE
    let c : c_elim2_ShiftCoord E :=
      ⟨(i, c_elim2_boxBranchFull E ω i), Or.inr hiE⟩
    have hc : c.val ≠ (R, 0) := by
      intro heq
      exact hiR (congrArg Prod.fst heq)
    have hsame (t : Fin L) :
        c_elim2_boxOldEndpointAssignment E R L o t c =
          o ⟨c, hc⟩ := by
      change (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t) c = _
      exact c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except
        E R L o t ⟨c, hc⟩
    have hcoord :
        (⟨(i, c_elim2_boxBranchFull (insert R E)
            ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) i),
          Or.inr (Finset.mem_insert_of_mem hiE)⟩ :
          c_elim2_ShiftCoord (insert R E)) =
        c_elim2_shiftCoordInsertOld E R c := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hbranchOld i hiE
    unfold c_elim2_boxShiftValue
    simp only [dif_pos (Finset.mem_insert_of_mem hiE), dif_pos hiE]
    exact congrArg Fin.val <| calc
      c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
          ⟨(i, c_elim2_boxBranchFull (insert R E)
            ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) i),
            Or.inr (Finset.mem_insert_of_mem hiE)⟩ =
        c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
          (c_elim2_shiftCoordInsertOld E R c) :=
            congrArg (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁) hcoord
      _ = c_elim2_boxOldEndpointAssignment E R L o t₀ c :=
            c_elim2_boxEndpointAssignment_old_eval E R hR L o t₀ t₁ c
      _ = c_elim2_boxOldEndpointAssignment E R L o
            (c_elim2_boxEndpointChoice t₀ t₁ b) c := by
              rw [hsame t₀, hsame (c_elim2_boxEndpointChoice t₀ t₁ b)]
  · by_cases hiR : i = R
    · subst i
      have hmemNew : R ∈ insert R E := Finset.mem_insert_self R E
      let c : c_elim2_ShiftCoord E := ⟨(R, 0), Or.inl rfl⟩
      by_cases hb : b.val = 0
      · have hbFin : b = 0 := Fin.ext hb
        have hcoord :
            (⟨(R, c_elim2_boxBranchFull (insert R E)
              ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R),
              Or.inr (Finset.mem_insert_self R E)⟩ :
              c_elim2_ShiftCoord (insert R E)) =
              c_elim2_shiftCoordInsertOld E R c := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · calc
              c_elim2_boxBranchFull (insert R E)
                  ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R = b := hbranchNew
              _ = 0 := hbFin
        unfold c_elim2_boxShiftValue
        simp only [dif_pos hmemNew, dif_neg hiE]
        exact congrArg Fin.val <| calc
          c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
              ⟨(R, c_elim2_boxBranchFull (insert R E)
                ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R),
                Or.inr hmemNew⟩ =
            c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
              (c_elim2_shiftCoordInsertOld E R c) :=
                congrArg (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁) hcoord
          _ = c_elim2_boxOldEndpointAssignment E R L o t₀ c :=
                c_elim2_boxEndpointAssignment_old_eval E R hR L o t₀ t₁ c
          _ = c_elim2_boxOldEndpointAssignment E R L o
                (c_elim2_boxEndpointChoice t₀ t₁ b) c := by
                  simp [c_elim2_boxOldEndpointAssignment, c_elim2_boxEndpointChoice,
                    c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_point, hbFin]
      · have hbval : b.val = 1 := by omega
        have hbFin : b = 1 := Fin.ext hbval
        have hcoord :
            (⟨(R, c_elim2_boxBranchFull (insert R E)
              ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R),
              Or.inr (Finset.mem_insert_self R E)⟩ :
              c_elim2_ShiftCoord (insert R E)) =
              c_elim2_shiftCoordInsertExtra E R := by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · calc
              c_elim2_boxBranchFull (insert R E)
                  ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R = b := hbranchNew
              _ = 1 := hbFin
        unfold c_elim2_boxShiftValue
        simp only [dif_pos hmemNew, dif_neg hiE]
        exact congrArg Fin.val <| calc
          c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
              ⟨(R, c_elim2_boxBranchFull (insert R E)
                ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, b)) R),
                Or.inr hmemNew⟩ =
            c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
              (c_elim2_shiftCoordInsertExtra E R) :=
                congrArg (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁) hcoord
          _ = t₁ := c_elim2_boxEndpointAssignment_extra_eval E R hR L o t₀ t₁
          _ = c_elim2_boxOldEndpointAssignment E R L o
                (c_elim2_boxEndpointChoice t₀ t₁ b) c := by
                  rw [hbFin]
                  change t₁ =
                    (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₁)
                      ⟨(R, 0), Or.inl rfl⟩
                  exact (c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_point
                    E R L o t₁).symm
    · let c : c_elim2_ShiftCoord E := ⟨(i, 0), Or.inl rfl⟩
      have hc : c.val ≠ (R, 0) := by
        intro heq
        exact hiR (congrArg Prod.fst heq)
      have hiInsert : i ∉ insert R E := by
        simpa [Finset.mem_insert, hiR] using hiE
      have hcoord :
          (⟨(i, 0), Or.inl rfl⟩ : c_elim2_ShiftCoord (insert R E)) =
            c_elim2_shiftCoordInsertOld E R c := by
        apply Subtype.ext
        rfl
      have hsame (t : Fin L) :
          c_elim2_boxOldEndpointAssignment E R L o t c =
            o ⟨c, hc⟩ := by
        change (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t) c = _
        exact c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except
          E R L o t ⟨c, hc⟩
      unfold c_elim2_boxShiftValue
      simp only [dif_neg hiInsert, dif_neg hiE]
      exact congrArg Fin.val <| calc
        c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
            ⟨(i, 0), Or.inl rfl⟩ =
          c_elim2_boxEndpointAssignment E R hR L o t₀ t₁
            (c_elim2_shiftCoordInsertOld E R c) :=
              congrArg (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁) hcoord
        _ = c_elim2_boxOldEndpointAssignment E R L o t₀ c :=
              c_elim2_boxEndpointAssignment_old_eval E R hR L o t₀ t₁ c
        _ = o ⟨c, hc⟩ := hsame t₀
        _ = c_elim2_boxOldEndpointAssignment E R L o
              (c_elim2_boxEndpointChoice t₀ t₁ b) c :=
                (hsame (c_elim2_boxEndpointChoice t₀ t₁ b)).symm

theorem c_elim2_boxTargetArgument_endpoint {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b))
    (ω : c_elim2_BoxBranch E) (bit : Fin 2) :
    c_elim2_boxTargetArgument D (insert R E) b
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
      ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, bit)) =
    c_elim2_boxTargetArgument D E b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
        (c_elim2_boxEndpointChoice t₀ t₁ bit)) ω := by
  unfold c_elim2_boxTargetArgument
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [c_elim2_boxShiftValue_endpoint]

theorem c_elim2_boxRowArgument_endpoint {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β) (I : α)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b))
    (ω : c_elim2_BoxBranch E) (bit : Fin 2) :
    c_elim2_boxRowArgument D (insert R E) b I
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
      (c_elim2_boxBranchFull (insert R E)
        ((c_elim2_boxBranchInsertEquiv E R hR).symm (ω, bit))) =
    c_elim2_boxRowArgument D E b I
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
        (c_elim2_boxEndpointChoice t₀ t₁ bit))
      (c_elim2_boxBranchFull E ω) := by
  unfold c_elim2_boxRowArgument
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [c_elim2_boxShiftValue_endpoint]

theorem c_elim2_boxTargetProduct_insert_endpoint {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxTargetProduct D (insert R E) b
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁) =
    ∏ bit : Fin 2, c_elim2_boxTargetProduct D E b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
        (c_elim2_boxEndpointChoice t₀ t₁ bit)) := by
  classical
  let e := c_elim2_boxBranchInsertEquiv E R hR
  unfold c_elim2_boxTargetProduct
  calc
    _ = ∏ p : c_elim2_BoxBranch E × Fin 2,
        D.targetFunction b (c_elim2_boxTargetArgument D (insert R E) b
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (e.symm p)) := by
      exact Fintype.prod_equiv e _ _ (by intro ω; simp [e])
    _ = ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
        D.targetFunction b (c_elim2_boxTargetArgument D (insert R E) b
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (e.symm (ω, bit))) := by
      calc
        ∏ p : c_elim2_BoxBranch E × Fin 2,
            D.targetFunction b (c_elim2_boxTargetArgument D (insert R E) b
              (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
              (e.symm p))
            = ∏ p : Fin 2 × c_elim2_BoxBranch E,
            D.targetFunction b (c_elim2_boxTargetArgument D (insert R E) b
              (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
              (e.symm (p.2, p.1))) := by
                exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (by intro p; rfl)
        _ = _ := Fintype.prod_prod_type _
    _ = ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
        D.targetFunction b (c_elim2_boxTargetArgument D E b
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
            (c_elim2_boxEndpointChoice t₀ t₁ bit)) ω) := by
      apply Fintype.prod_congr
      intro bit
      apply Fintype.prod_congr
      intro ω
      rw [c_elim2_boxTargetArgument_endpoint]
    _ = _ := rfl

theorem c_elim2_fintype_prod_comm {α β γ : Type*} [Fintype α] [Fintype β]
    [CommMonoid γ] (F : α → β → γ) :
    (∏ a, ∏ b, F a b) = ∏ b, ∏ a, F a b := by
  calc
    (∏ a, ∏ b, F a b) = ∏ p : α × β, F p.1 p.2 :=
      (Fintype.prod_prod_type (fun p : α × β => F p.1 p.2)).symm
    _ = ∏ p : β × α, F p.2 p.1 :=
      Fintype.prod_equiv (Equiv.prodComm α β) _ _ (by intro p; rfl)
    _ = ∏ b, ∏ a, F a b :=
      Fintype.prod_prod_type (fun p : β × α => F p.2 p.1)

noncomputable def c_elim2_activeRowInsertEquiv {α : Type u} [DecidableEq α]
    (E : Finset α) (R : α) :
    c_elim2_ActiveRowIndex (insert R E) ≃ c_elim2_ActiveRowIndexExcept E R := by
  classical
  refine Equiv.subtypeEquivRight ?_
  intro i
  simp [Finset.mem_insert, eq_comm, and_comm]

theorem c_elim2_boxActiveRowFactor_insert_endpoint {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R I : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    (∏ ω : c_elim2_BoxBranch (insert R E),
      D.rowFunction I b
        (c_elim2_boxRowArgument D (insert R E) b I
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (c_elim2_boxBranchFull (insert R E) ω))) =
    ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
      D.rowFunction I b
        (c_elim2_boxRowArgument D E b I
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
            (c_elim2_boxEndpointChoice t₀ t₁ bit))
          (c_elim2_boxBranchFull E ω)) := by
  classical
  let e := c_elim2_boxBranchInsertEquiv E R hR
  calc
    _ = ∏ p : c_elim2_BoxBranch E × Fin 2,
        D.rowFunction I b
          (c_elim2_boxRowArgument D (insert R E) b I
            (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
            (c_elim2_boxBranchFull (insert R E) (e.symm p))) := by
      exact Fintype.prod_equiv e _ _ (by intro ω; simp [e])
    _ = ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
        D.rowFunction I b
          (c_elim2_boxRowArgument D (insert R E) b I
            (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
            (c_elim2_boxBranchFull (insert R E) (e.symm (ω, bit)))) := by
      calc
        ∏ p : c_elim2_BoxBranch E × Fin 2,
            D.rowFunction I b
              (c_elim2_boxRowArgument D (insert R E) b I
                (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
                (c_elim2_boxBranchFull (insert R E) (e.symm p)))
            = ∏ p : Fin 2 × c_elim2_BoxBranch E,
              D.rowFunction I b
                (c_elim2_boxRowArgument D (insert R E) b I
                  (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
                  (c_elim2_boxBranchFull (insert R E) (e.symm (p.2, p.1)))) := by
              exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (by intro p; rfl)
        _ = _ := Fintype.prod_prod_type _
    _ = ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
        D.rowFunction I b
          (c_elim2_boxRowArgument D E b I
            (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
              (c_elim2_boxEndpointChoice t₀ t₁ bit))
            (c_elim2_boxBranchFull E ω)) := by
      apply Fintype.prod_congr
      intro bit
      apply Fintype.prod_congr
      intro ω
      rw [c_elim2_boxRowArgument_endpoint]

theorem c_elim2_boxActiveProduct_insert_endpoint {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxActiveProduct D (insert R E) b
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁) =
    ∏ bit : Fin 2, c_elim2_boxOtherActiveProduct D E R b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
        (c_elim2_boxEndpointChoice t₀ t₁ bit)) := by
  classical
  let eI := c_elim2_activeRowInsertEquiv E R
  have hindex :
      (∏ I : c_elim2_ActiveRowIndex (insert R E),
        ∏ ω : c_elim2_BoxBranch (insert R E),
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D (insert R E) b I.1
              (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
              (c_elim2_boxBranchFull (insert R E) ω))) =
      ∏ I : c_elim2_ActiveRowIndexExcept E R,
        ∏ ω : c_elim2_BoxBranch (insert R E),
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D (insert R E) b I.1
              (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
              (c_elim2_boxBranchFull (insert R E) ω)) := by
    exact Fintype.prod_equiv eI _ _
      (by intro I; simp [eI, c_elim2_activeRowInsertEquiv])
  unfold c_elim2_boxActiveProduct c_elim2_boxOtherActiveProduct
  calc
    _ = ∏ I : c_elim2_ActiveRowIndexExcept E R,
        ∏ ω : c_elim2_BoxBranch (insert R E),
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D (insert R E) b I.1
              (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
              (c_elim2_boxBranchFull (insert R E) ω)) := hindex
    _ = ∏ I : c_elim2_ActiveRowIndexExcept E R,
        ∏ bit : Fin 2, ∏ ω : c_elim2_BoxBranch E,
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D E b I.1
              (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
                (c_elim2_boxEndpointChoice t₀ t₁ bit))
              (c_elim2_boxBranchFull E ω)) := by
      apply Fintype.prod_congr
      intro I
      simpa using c_elim2_boxActiveRowFactor_insert_endpoint D E R I.1 hR b o t₀ t₁
    _ = ∏ bit : Fin 2, ∏ I : c_elim2_ActiveRowIndexExcept E R,
        ∏ ω : c_elim2_BoxBranch E,
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D E b I.1
              (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
                (c_elim2_boxEndpointChoice t₀ t₁ bit))
              (c_elim2_boxBranchFull E ω)) := by
      let rowFactor : c_elim2_ActiveRowIndexExcept E R → Fin 2 → ℝ := fun I bit =>
        ∏ ω : c_elim2_BoxBranch E,
          D.rowFunction I.1 b
            (c_elim2_boxRowArgument D E b I.1
              (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
                (c_elim2_boxEndpointChoice t₀ t₁ bit))
              (c_elim2_boxBranchFull E ω))
      simpa [rowFactor] using c_elim2_fintype_prod_comm rowFactor
    _ = _ := rfl

theorem c_elim2_boxRetainedRowArgument_insert_endpoint {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R I : α) (hR : R ∉ E) (hI : I ∈ E)
    (b : β) (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) (η : c_elim2_BoxRetainedBranch E I)
    (bit : Fin 2) :
    c_elim2_boxRowArgument D (insert R E) b I
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
      (c_elim2_boxRetainedBranchFull (insert R E) I
        ((c_elim2_boxRetainedBranchInsertEquiv E R I hR hI).symm (η, bit))) =
    c_elim2_boxRowArgument D E b I
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
        (c_elim2_boxEndpointChoice t₀ t₁ bit))
      (c_elim2_boxRetainedBranchFull E I η) := by
  classical
  let ω : c_elim2_BoxBranch E := fun j =>
    if hj : j.val ∈ E.erase I then η ⟨j.val, hj⟩ else 0
  let η' := (c_elim2_boxRetainedBranchInsertEquiv E R I hR hI).symm (η, bit)
  let ω' := (c_elim2_boxBranchInsertEquiv E R hR).symm (ω, bit)
  have hω (j : α) :
      c_elim2_boxBranchFull E ω j = c_elim2_boxRetainedBranchFull E I η j := by
    by_cases hjE : j ∈ E
    · by_cases hjErase : j ∈ E.erase I
      · have hjNotI : j ≠ I := (Finset.mem_erase.mp hjErase).1
        simp [c_elim2_boxBranchFull, c_elim2_boxRetainedBranchFull, ω,
          hjE, hjErase, hjNotI]
      · have hji : j = I := by
          by_contra hne
          exact hjErase (Finset.mem_erase.mpr ⟨hne, hjE⟩)
        simp [c_elim2_boxBranchFull, c_elim2_boxRetainedBranchFull, ω,
          hjE, hjErase, hji]
    · have hjErase : j ∉ E.erase I := by
        intro h
        exact hjE (Finset.mem_erase.mp h).2
      simp [c_elim2_boxBranchFull, c_elim2_boxRetainedBranchFull, ω,
        hjE, hjErase]
  have hbranch (j : α) (hjI : j ≠ I) :
      c_elim2_boxRetainedBranchFull (insert R E) I η' j =
        c_elim2_boxBranchFull (insert R E) ω' j := by
    by_cases hjIns : j ∈ insert R E
    · have hjErase : j ∈ (insert R E).erase I :=
        Finset.mem_erase.mpr ⟨hjI, hjIns⟩
      rcases Finset.mem_insert.mp hjIns with hjR | hjE
      · subst j
        have hleft : η' ⟨R, hjErase⟩ = bit := by
          simpa [η'] using
            c_elim2_boxRetainedBranchInsertEquiv_symm_apply_new
              E R I hR hI η bit
        have hright : ω' ⟨R, Finset.mem_insert_self R E⟩ = bit := by
          simpa [ω'] using c_elim2_boxBranchInsertEquiv_symm_apply_new
            E R hR ω bit
        simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
          η', ω', hjErase, hjIns, hleft, hright]
      · have hjEraseE : j ∈ E.erase I :=
          Finset.mem_erase.mpr ⟨hjI, hjE⟩
        have hleft : η' ⟨j, hjErase⟩ = η ⟨j, hjEraseE⟩ := by
          simpa [η'] using
            c_elim2_boxRetainedBranchInsertEquiv_symm_apply_old
              E R I hR hI η bit ⟨j, hjEraseE⟩
        have hright : ω' ⟨j, Finset.mem_insert_of_mem hjE⟩ =
            ω ⟨j, hjE⟩ := by
          simpa [ω'] using c_elim2_boxBranchInsertEquiv_symm_apply_old
            E R hR ω bit ⟨j, hjE⟩
        have hωj : ω ⟨j, hjE⟩ = η ⟨j, hjEraseE⟩ := by
          have hjNotI : j ≠ I := (Finset.mem_erase.mp hjEraseE).1
          simp [ω, hjEraseE, hjNotI]
        simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
          η', ω', hjErase, hjIns, hleft, hright, hωj]
    · have hjErase : j ∉ (insert R E).erase I := by
        simp [Finset.mem_erase, hjIns]
      simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
        η', ω', hjErase, hjIns]
  have hbranchAtI :
      c_elim2_boxRetainedBranchFull (insert R E) I η' I =
        c_elim2_boxBranchFull (insert R E) ω' I := by
    have hIerase : I ∉ (insert R E).erase I := by simp
    have hproj : ω' ⟨I, Finset.mem_insert_of_mem hI⟩ = ω ⟨I, hI⟩ := by
      simpa [ω'] using c_elim2_boxBranchInsertEquiv_symm_apply_old
        E R hR ω bit ⟨I, hI⟩
    have hw : ω ⟨I, hI⟩ = 0 := by simp [ω]
    simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
      η', ω', hIerase, hI, hproj, hw]
  have hbranchFun :
      c_elim2_boxRetainedBranchFull (insert R E) I η' =
        c_elim2_boxBranchFull (insert R E) ω' := by
    funext j
    by_cases hjI : j = I
    · subst j
      exact hbranchAtI
    · exact hbranch j hjI
  have hωFun : c_elim2_boxBranchFull E ω =
      c_elim2_boxRetainedBranchFull E I η := by
    funext j
    exact hω j
  unfold c_elim2_boxRowArgument
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjI : j ≠ I := (Finset.mem_erase.mp hj).1
  calc
    (D.rowCoefficient I j b : ℚ) *
        (c_elim2_boxShiftValue (insert R E)
        (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
        (c_elim2_boxRetainedBranchFull (insert R E) I η') j : ℚ) =
      (D.rowCoefficient I j b : ℚ) *
        (c_elim2_boxShiftValue (insert R E)
        (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
        (c_elim2_boxBranchFull (insert R E) ω') j : ℚ) := by rw [hbranchFun]
    _ = (D.rowCoefficient I j b : ℚ) *
        (c_elim2_boxShiftValue E
        (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
          (c_elim2_boxEndpointChoice t₀ t₁ bit))
        (c_elim2_boxBranchFull E ω) j : ℚ) := by
          rw [c_elim2_boxShiftValue_endpoint E R hR (D.shiftLength b) o t₀ t₁ ω bit j]
    _ = (D.rowCoefficient I j b : ℚ) *
        (c_elim2_boxShiftValue E
        (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
          (c_elim2_boxEndpointChoice t₀ t₁ bit))
        (c_elim2_boxRetainedBranchFull E I η) j : ℚ) := by rw [hωFun]

theorem c_elim2_boxRetainedRowFactor_insert_endpoint {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R I : α) (hR : R ∉ E) (hI : I ∈ E)
    (b : β) (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    (∏ η : c_elim2_BoxRetainedBranch (insert R E) I,
      D.rowWeight I b
        (c_elim2_boxRowArgument D (insert R E) b I
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (c_elim2_boxRetainedBranchFull (insert R E) I η))) =
    ∏ bit : Fin 2, ∏ η : c_elim2_BoxRetainedBranch E I,
      D.rowWeight I b
        (c_elim2_boxRowArgument D E b I
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
            (c_elim2_boxEndpointChoice t₀ t₁ bit))
          (c_elim2_boxRetainedBranchFull E I η)) := by
  classical
  let e := c_elim2_boxRetainedBranchInsertEquiv E R I hR hI
  calc
    _ = ∏ p : c_elim2_BoxRetainedBranch E I × Fin 2,
        D.rowWeight I b
          (c_elim2_boxRowArgument D (insert R E) b I
            (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
            (c_elim2_boxRetainedBranchFull (insert R E) I (e.symm p))) := by
      exact Fintype.prod_equiv e _ _ (by intro η; simp)
    _ = ∏ bit : Fin 2, ∏ η : c_elim2_BoxRetainedBranch E I,
        D.rowWeight I b
          (c_elim2_boxRowArgument D (insert R E) b I
            (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
            (c_elim2_boxRetainedBranchFull (insert R E) I (e.symm (η, bit)))) := by
      calc
        ∏ p : c_elim2_BoxRetainedBranch E I × Fin 2,
            D.rowWeight I b
              (c_elim2_boxRowArgument D (insert R E) b I
                (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
                (c_elim2_boxRetainedBranchFull (insert R E) I (e.symm p)))
            = ∏ p : Fin 2 × c_elim2_BoxRetainedBranch E I,
              D.rowWeight I b
                (c_elim2_boxRowArgument D (insert R E) b I
                  (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
                  (c_elim2_boxRetainedBranchFull (insert R E) I (e.symm (p.2, p.1)))) := by
              exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (by intro p; rfl)
        _ = _ := Fintype.prod_prod_type _
    _ = ∏ bit : Fin 2, ∏ η : c_elim2_BoxRetainedBranch E I,
        D.rowWeight I b
          (c_elim2_boxRowArgument D E b I
            (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
              (c_elim2_boxEndpointChoice t₀ t₁ bit))
            (c_elim2_boxRetainedBranchFull E I η)) := by
      apply Fintype.prod_congr
      intro bit
      apply Fintype.prod_congr
      intro η
      rw [c_elim2_boxRetainedRowArgument_insert_endpoint]

theorem c_elim2_boxRetainedInsertedRowFactor_endpoint {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    (∏ η : c_elim2_BoxRetainedBranch (insert R E) R,
      D.rowWeight R b
        (c_elim2_boxRowArgument D (insert R E) b R
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (c_elim2_boxRetainedBranchFull (insert R E) R η))) =
    c_elim2_boxWeightRowFactor D E R b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) := by
  classical
  let eDom : {j : α // j ∈ (insert R E).erase R} ≃ {j : α // j ∈ E} :=
    Equiv.subtypeEquivRight (fun j => by
      simp [Finset.mem_erase, hR, eq_comm])
  let e : c_elim2_BoxRetainedBranch (insert R E) R ≃ c_elim2_BoxBranch E :=
    Equiv.arrowCongr eDom (Equiv.refl (Fin 2))
  let ω' (ω : c_elim2_BoxBranch E) : c_elim2_BoxBranch (insert R E) :=
    (c_elim2_boxBranchInsertEquiv E R hR).symm (ω, 0)
  have hfull (ω : c_elim2_BoxBranch E) :
      c_elim2_boxRetainedBranchFull (insert R E) R (e.symm ω) =
        c_elim2_boxBranchFull (insert R E) (ω' ω) := by
    funext j
    by_cases hjR : j = R
    · subst j
      have hbranchR : ω' ω ⟨R, Finset.mem_insert_self R E⟩ = 0 := by
        simpa [ω'] using c_elim2_boxBranchInsertEquiv_symm_apply_new
          E R hR ω 0
      simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull, ω',
        Finset.mem_erase, hR, hbranchR]
    · by_cases hjE : j ∈ E
      · have hjErase : j ∈ (insert R E).erase R := by
          simp [Finset.mem_erase, hjR, hjE]
        have heDom : eDom ⟨j, hjErase⟩ = ⟨j, hjE⟩ := by
          apply Subtype.ext
          rfl
        have heval : (e.symm ω) ⟨j, hjErase⟩ = ω ⟨j, hjE⟩ := by
          change ω (eDom ⟨j, hjErase⟩) = ω ⟨j, hjE⟩
          rw [heDom]
        have hbranch : ω' ω ⟨j, Finset.mem_insert_of_mem hjE⟩ = ω ⟨j, hjE⟩ := by
          simpa [ω', hjR] using c_elim2_boxBranchInsertEquiv_symm_apply_old
            E R hR ω 0 ⟨j, hjE⟩
        simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
          ω', hjR, hjErase, hjE, heval, hbranch]
      · have hjIns : j ∉ insert R E := by
          simp [Finset.mem_insert, hjR, hjE]
        simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull,
          ω', e, eDom, hjIns, hjE]
  calc
    _ = ∏ ω : c_elim2_BoxBranch E,
        D.rowWeight R b
          (c_elim2_boxRowArgument D (insert R E) b R
            (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
            (c_elim2_boxRetainedBranchFull (insert R E) R (e.symm ω))) := by
      exact Fintype.prod_equiv e _ _ (by intro η; simp)
    _ = ∏ ω : c_elim2_BoxBranch E,
        D.rowWeight R b
          (c_elim2_boxRowArgument D E b R
            (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀)
            (c_elim2_boxBranchFull E ω)) := by
      apply Fintype.prod_congr
      intro ω
      rw [hfull ω, c_elim2_boxRowArgument_endpoint]
      simp [c_elim2_boxEndpointChoice]
    _ = _ := rfl

theorem c_elim2_boxRetainedProduct_insert_endpoint {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxRetainedProduct D (insert R E) b
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁) =
    c_elim2_boxWeightRowFactor D E R b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) *
      ∏ bit : Fin 2, c_elim2_boxRetainedProduct D E b
        (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
          (c_elim2_boxEndpointChoice t₀ t₁ bit)) := by
  classical
  let eI := c_elim2_finsetSubtypeInsertEquiv E R hR
  let newFactor (I : {i : α // i ∈ insert R E}) : ℝ :=
    ∏ η : c_elim2_BoxRetainedBranch (insert R E) I.1,
      D.rowWeight I.1 b
        (c_elim2_boxRowArgument D (insert R E) b I.1
          (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁)
          (c_elim2_boxRetainedBranchFull (insert R E) I.1 η))
  let oldFactor (I : {i : α // i ∈ E}) (bit : Fin 2) : ℝ :=
    ∏ η : c_elim2_BoxRetainedBranch E I.1,
      D.rowWeight I.1 b
        (c_elim2_boxRowArgument D E b I.1
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
            (c_elim2_boxEndpointChoice t₀ t₁ bit))
          (c_elim2_boxRetainedBranchFull E I.1 η))
  have hsplit :
      (∏ I : {i : α // i ∈ insert R E}, newFactor I) =
        (∏ I : {i : α // i ∈ E}, newFactor (eI.symm (Sum.inl I))) *
          newFactor (eI.symm (Sum.inr PUnit.unit)) := by
    calc
      _ = ∏ x : {i : α // i ∈ E} ⊕ PUnit.{u + 1}, newFactor (eI.symm x) := by
        exact Fintype.prod_equiv eI _ _ (by intro I; simp [eI])
      _ = _ := by rw [Fintype.prod_sum_type]; simp
  have hOld (I : {i : α // i ∈ E}) :
      newFactor (eI.symm (Sum.inl I)) = ∏ bit : Fin 2, oldFactor I bit := by
    simpa [newFactor, oldFactor, eI, c_elim2_finsetSubtypeInsertEquiv] using
      c_elim2_boxRetainedRowFactor_insert_endpoint
        D E R I.val hR I.property b o t₀ t₁
  have hNew : newFactor (eI.symm (Sum.inr PUnit.unit)) =
      c_elim2_boxWeightRowFactor D E R b
        (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) := by
    simpa [newFactor, eI, c_elim2_finsetSubtypeInsertEquiv] using
      c_elim2_boxRetainedInsertedRowFactor_endpoint D E R hR b o t₀ t₁
  have holdprod :
      (∏ I : {i : α // i ∈ E}, newFactor (eI.symm (Sum.inl I))) =
        ∏ I : {i : α // i ∈ E}, ∏ bit : Fin 2, oldFactor I bit := by
    apply Fintype.prod_congr
    intro I
    exact hOld I
  calc
    c_elim2_boxRetainedProduct D (insert R E) b
        (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁) =
      (∏ I : {i : α // i ∈ E}, newFactor (eI.symm (Sum.inl I))) *
        newFactor (eI.symm (Sum.inr PUnit.unit)) := by
          unfold c_elim2_boxRetainedProduct
          exact hsplit
    _ = (∏ I : {i : α // i ∈ E}, ∏ bit : Fin 2, oldFactor I bit) *
        c_elim2_boxWeightRowFactor D E R b
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) := by
          rw [holdprod, hNew]
    _ = c_elim2_boxWeightRowFactor D E R b
          (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) *
        ∏ bit : Fin 2, ∏ I : {i : α // i ∈ E}, oldFactor I bit := by
          rw [c_elim2_fintype_prod_comm (fun I bit => oldFactor I bit)]
          ring
    _ = _ := by
      congr 1

theorem c_elim2_boxEraseInsert {α : Type u} [DecidableEq α]
    (E : Finset α) (R I : α) (hR : R ∉ E) (hI : I ∈ E) :
    (insert R E).erase I = insert R (E.erase I) := by
  have hRI : R ≠ I := by
    intro heq
    subst I
    exact hR hI
  exact Finset.erase_insert_of_ne hRI

/-- The pointwise target-cube product is bounded by its product of divisor weights. -/
theorem c_elim2_target_cube_product_abs_le_targetBound
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (p : Fin q → ℕ) (z : Fin m → ℚ) (u : NonTarget Sh → Fin 2 → ℕ)
    (g : ℤ → ℝ)
    (hg : ∀ y, |g y| ≤ 1 + chainWeight S.core.parameters C N
      (Sh.row Sh.star).anchor y) :
    |∏ ω : NonTarget Sh → Fin 2,
        atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω)| ≤
      targetBound S C a N dirs p z u := by
  classical
  have hfactor (ω : NonTarget Sh → Fin 2) :
      |atQ g (targetVertex (chainScale S.core.parameters C a N) Sh p
        (directionModulus S N dirs.poly p) z u ω)| ≤
      1 + atQ (chainWeight S.core.parameters C N (Sh.row Sh.star).anchor)
        (targetVertex (chainScale S.core.parameters C a N) Sh p
          (directionModulus S N dirs.poly p) z u ω) := by
    let x := targetVertex (chainScale S.core.parameters C a N) Sh p
      (directionModulus S N dirs.poly p) z u ω
    by_cases hx : x.den = 1
    · simpa [atQ, x, hx] using hg x.num
    · simp [atQ, x, hx]
  rw [Finset.abs_prod]
  unfold targetBound
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    (fun ω _ => hfactor ω)

end HindmanSumsProducts
