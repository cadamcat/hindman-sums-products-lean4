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
  let eCoord := c_elim2_shiftCoord_split_equiv E R
  exact (Equiv.arrowCongr eCoord (Equiv.refl (Fin L))).trans
    ((Equiv.sumArrowEquivProdArrow (c_elim2_ShiftCoordExcept E R) PUnit.{u + 1} (Fin L)).trans
      (Equiv.prodCongr (Equiv.refl (c_elim2_ShiftCoordExcept E R → Fin L))
        (Equiv.punitArrowEquiv (Fin L))) )

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
