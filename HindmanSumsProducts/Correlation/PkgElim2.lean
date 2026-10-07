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

theorem c_elim2_rowForm_finset_sum {m q : ℕ} {ι : Type*} [DecidableEq ι]
    (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (U : Finset ι) (a : ι → ℚ)
    (v : ι → Fin m → ℚ) :
    rowForm c T p (fun k => z k + ∑ i ∈ U, a i * v i k) =
      rowForm c T p z + ∑ i ∈ U, a i * rowForm c T p (v i) := by
  classical
  let w : Fin m → ℚ := fun k => c k / c T.anchor * T.value p k
  change (∑ k, w k * (z k + ∑ i ∈ U, a i * v i k)) =
    (∑ k, w k * z k) + ∑ i ∈ U, a i * ∑ k, w k * v i k
  have hswap :
      (∑ k : Fin m, w k * ∑ i ∈ U, a i * v i k) =
        ∑ i ∈ U, a i * ∑ k : Fin m, w k * v i k := by
    calc
      _ = ∑ k : Fin m, ∑ i ∈ U, a i * (w k * v i k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i ∈ U, ∑ k : Fin m, a i * (w k * v i k) := by
        exact Finset.sum_comm
      _ = ∑ i ∈ U, a i * ∑ k : Fin m, w k * v i k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
  calc
    _ = (∑ k, w k * z k) + ∑ k : Fin m, w k * ∑ i ∈ U, a i * v i k := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = (∑ k, w k * z k) + ∑ i ∈ U, a i * ∑ k : Fin m, w k * v i k := by
      rw [hswap]
    _ = _ := by simp [rowForm, w]

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

def c_elim2_pivotSupport {K m : ℕ} (A : OAI.SourceAdmissible.Parameters K)
    (C : MasterChain K m) (N : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun k : Fin m =>
    Finset.Icc 0 ((A.X N (C.block k).1 ^ 2 : ℕ) : ℤ)

theorem c_elim2_pivotMass_zero_of_not_mem_support {K m : ℕ}
    (A : OAI.SourceAdmissible.Parameters K) (C : MasterChain K m)
    (N : ℕ) (z : Fin m → ℤ) (hz : z ∉ c_elim2_pivotSupport A C N) :
    pivotMass A C N z = 0 := by
  classical
  have hnotall : ¬ ∀ k : Fin m,
      z k ∈ Finset.Icc 0 ((A.X N (C.block k).1 ^ 2 : ℕ) : ℤ) := by
    intro hall
    apply hz
    simpa [c_elim2_pivotSupport] using hall
  obtain ⟨k, hk⟩ := not_forall.mp hnotall
  unfold pivotMass
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  unfold harmonicLaw
  split_ifs with h
  · apply False.elim
    apply hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact h.1
    · have hEq : ((z k).toNat : ℤ) = z k := Int.toNat_of_nonneg h.1
      rw [← hEq]
      exact_mod_cast (Nat.le_of_lt h.2.2.1)
  · rfl

def c_elim2_independentPrimeSupport {q : ℕ} (lo hi : Fin q → ℕ) :
    Finset (Fin q → ℕ) :=
  Fintype.piFinset fun i : Fin q => Finset.Ico (lo i) (hi i)

theorem c_elim2_independentPrimePoolMass_zero_of_not_mem_support {q : ℕ}
    (lo hi : Fin q → ℕ) (p : Fin q → ℕ)
    (hp : p ∉ c_elim2_independentPrimeSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin q, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [c_elim2_independentPrimeSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

noncomputable def c_elim2_goodIndicator {K m q r s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (p : Fin q → ℕ) : ℝ := by
  classical
  exact if GoodTuple S C.gap N tests dirs.poly p then 1 else 0

theorem c_elim2_eliminationAverage_eq_finiteOuterSupport
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ)
    (F : (Fin q → ℕ) → (Fin m → ℚ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
    eliminationAverage S C N dirs tests J0 F =
      (gapSlotProbability S C.gap N (GoodTuple S C.gap N tests dirs.poly))⁻¹ *
        ∑ p : {p : Fin q → ℕ // p ∈ c_elim2_independentPrimeSupport
            (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
            (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)},
          ∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
            gapSlotMass S C.gap N p.1 *
              c_elim2_goodIndicator S C N Sh dirs tests p.1 *
              pivotMass S.core.parameters C N z.1 *
              shiftAverage (NonTarget Sh)
                (shiftLength S C.gap J0 N dirs.poly p.1)
                (F p.1 (fun k => (z.1 k : ℚ))) := by
  classical
  let Good : (Fin q → ℕ) → Prop := GoodTuple S C.gap N tests dirs.poly
  let Psupport : Finset (Fin q → ℕ) :=
    c_elim2_independentPrimeSupport
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let Zsupport : Finset (Fin m → ℤ) := c_elim2_pivotSupport S.core.parameters C N
  have hPzero (p : Fin q → ℕ) (hp : p ∉ Psupport) :
      gapSlotMass S C.gap N p = 0 := by
    simpa [gapSlotMass, Psupport] using
      c_elim2_independentPrimePoolMass_zero_of_not_mem_support
        (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
        (fun _ : Fin q => (S.primeStage.pool N C.gap).upper) p hp
  have hZzero (z : Fin m → ℤ) (hz : z ∉ Zsupport) :
      pivotMass S.core.parameters C N z = 0 := by
    exact c_elim2_pivotMass_zero_of_not_mem_support
      S.core.parameters C N z (by simpa [Zsupport] using hz)
  have hinner (p : Fin q → ℕ) :
      gapSlotMass S C.gap N p *
        (if Good p then ∑' z : Fin m → ℤ,
          pivotMass S.core.parameters C N z *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
              (F p (fun k => (z k : ℚ))) else 0) =
    ∑ z ∈ Zsupport,
        gapSlotMass S C.gap N p * c_elim2_goodIndicator S C N Sh dirs tests p *
          pivotMass S.core.parameters C N z *
          shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
            (F p (fun k => (z k : ℚ))) := by
    by_cases hpGood : Good p
    · have hGoodIndicator : c_elim2_goodIndicator S C N Sh dirs tests p = 1 := by
        simp [c_elim2_goodIndicator, Good, hpGood]
      simp [Good, hpGood, hGoodIndicator]
      have htsum :
          (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
              (F p (fun k => (z k : ℚ)))) =
          ∑ z ∈ Zsupport, pivotMass S.core.parameters C N z *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
              (F p (fun k => (z k : ℚ))) := by
        rw [tsum_eq_sum (fun z hz => by rw [hZzero z hz]; simp)]
      rw [htsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    · simp [hpGood, Good, c_elim2_goodIndicator]
  have hpSupportZero (p : Fin q → ℕ) (hp : p ∉ Psupport) :
      gapSlotMass S C.gap N p *
        (if Good p then ∑' z : Fin m → ℤ,
          pivotMass S.core.parameters C N z *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
              (F p (fun k => (z k : ℚ))) else 0) = 0 := by
    rw [hPzero p hp]
    simp
  calc
    _ = (gapSlotProbability S C.gap N Good)⁻¹ *
        ∑ p ∈ Psupport, gapSlotMass S C.gap N p *
          (if Good p then ∑' z : Fin m → ℤ,
            pivotMass S.core.parameters C N z *
              shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
                (F p (fun k => (z k : ℚ))) else 0) := by
      unfold eliminationAverage goodSlotAverage
      rw [tsum_eq_sum hpSupportZero]
    _ = (gapSlotProbability S C.gap N Good)⁻¹ *
        ∑ p ∈ Psupport, ∑ z ∈ Zsupport,
          gapSlotMass S C.gap N p * c_elim2_goodIndicator S C N Sh dirs tests p *
            pivotMass S.core.parameters C N z *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
              (F p (fun k => (z k : ℚ))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact hinner p
    _ = _ := by
      congr 1
      let g (p : Fin q → ℕ) (z : Fin m → ℤ) :=
        gapSlotMass S C.gap N p * c_elim2_goodIndicator S C N Sh dirs tests p *
          pivotMass S.core.parameters C N z *
          shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
            (F p (fun k => (z k : ℚ)))
      let ZSub := {z : Fin m → ℤ // z ∈ Zsupport}
      let PSub := {p : Fin q → ℕ // p ∈ Psupport}
      have hZsum (p : Fin q → ℕ) :
          (∑ z ∈ Zsupport, g p z) = ∑ z : ZSub, g p z.1 := by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach Zsupport (fun z => g p z)).symm
      have hPsum :
          (∑ p ∈ Psupport, ∑ z : ZSub, g p z.1) =
            ∑ p : PSub, ∑ z : ZSub, g p.1 z.1 := by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach Psupport (fun p => ∑ z : ZSub, g p z.1)).symm
      have hfinite :
          (∑ p ∈ Psupport, ∑ z ∈ Zsupport, g p z) =
            ∑ p ∈ Psupport, ∑ z : ZSub, g p z.1 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hZsum p
      rw [hfinite]
      exact hPsum

theorem c_elim2_subtype_sum_filter {P : Type*} [DecidableEq P]
    (s : Finset P) (G : P → Prop) [DecidablePred G] (f : P → ℝ) :
    (∑ p : {p // p ∈ s}, if G p.1 then f p.1 else 0) =
      ∑ p : {p // p ∈ s.filter G}, f p.1 := by
  classical
  calc
    (∑ p : {p // p ∈ s}, if G p.1 then f p.1 else 0) =
        ∑ p ∈ s, if G p then f p else 0 := by
          simpa only [Finset.attach_eq_univ] using
            (Finset.sum_attach s (fun p => if G p then f p else 0))
    _ = ∑ p ∈ s.filter G, f p := by rw [Finset.sum_filter]
    _ = ∑ p : {p // p ∈ s.filter G}, f p.1 := by
          simpa only [Finset.attach_eq_univ] using
            (Finset.sum_attach (s.filter G) f).symm

noncomputable def c_elim2_goodPrimeSupport
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) : Finset (Fin q → ℕ) := by
  classical
  exact (c_elim2_independentPrimeSupport
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)).filter
    (GoodTuple S C.gap N tests dirs.poly)

theorem c_elim2_eliminationAverage_eq_finiteGoodSupport
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (N : ℕ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 : ℕ)
    (F : (Fin q → ℕ) → (Fin m → ℚ) → (NonTarget Sh → Fin 2 → ℕ) → ℝ) :
      eliminationAverage S C N dirs tests J0 F =
      (gapSlotProbability S C.gap N (GoodTuple S C.gap N tests dirs.poly))⁻¹ *
        ∑ p : {p : Fin q → ℕ // p ∈
            c_elim2_goodPrimeSupport S C N Sh dirs tests},
          ∑ z : {z : Fin m → ℤ // z ∈ c_elim2_pivotSupport S.core.parameters C N},
            gapSlotMass S C.gap N p.1 * pivotMass S.core.parameters C N z.1 *
              shiftAverage (NonTarget Sh)
                (shiftLength S C.gap J0 N dirs.poly p.1)
                (F p.1 (fun k => (z.1 k : ℚ))) := by
  classical
  let Good : (Fin q → ℕ) → Prop := GoodTuple S C.gap N tests dirs.poly
  let Psupport : Finset (Fin q → ℕ) := c_elim2_independentPrimeSupport
    (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  let Zsupport : Finset (Fin m → ℤ) := c_elim2_pivotSupport S.core.parameters C N
  let PSub := {p : Fin q → ℕ // p ∈ Psupport}
  let ZSub := {z : Fin m → ℤ // z ∈ Zsupport}
  let PGood := {p : Fin q → ℕ // p ∈ c_elim2_goodPrimeSupport S C N Sh dirs tests}
  letI : DecidablePred Good := Classical.decPred Good
  rw [c_elim2_eliminationAverage_eq_finiteOuterSupport]
  congr 1
  have hsumP :
      (∑ p : PSub, ∑ z : ZSub,
        gapSlotMass S C.gap N p.1 * c_elim2_goodIndicator S C N Sh dirs tests p.1 *
          pivotMass S.core.parameters C N z.1 *
          shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p.1)
            (F p.1 (fun k => (z.1 k : ℚ)))) =
      ∑ p : PSub, if Good p.1 then
        gapSlotMass S C.gap N p.1 *
          ∑ z : ZSub, pivotMass S.core.parameters C N z.1 *
            shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p.1)
              (F p.1 (fun k => (z.1 k : ℚ)) ) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hgood : Good p.1
    · simp [c_elim2_goodIndicator, Good, hgood]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    · simp [c_elim2_goodIndicator, Good, hgood]
  have hfilter := c_elim2_subtype_sum_filter Psupport Good (fun p =>
    gapSlotMass S C.gap N p *
      ∑ z : ZSub, pivotMass S.core.parameters C N z.1 *
        shiftAverage (NonTarget Sh) (shiftLength S C.gap J0 N dirs.poly p)
          (F p (fun k => (z.1 k : ℚ))))
  rw [hsumP, hfilter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

noncomputable def c_elim2_shiftRangeEquiv {α : Type u} [Fintype α]
    [DecidableEq α] (L : ℕ) :
    (α → Fin 2 → Fin L) ≃
      {u : α → Fin 2 → ℕ // u ∈ Fintype.piFinset
        (fun _ : α => Fintype.piFinset (fun _ : Fin 2 => Finset.range L))} := by
  classical
  let S : Finset (α → Fin 2 → ℕ) := Fintype.piFinset
    (fun _ : α => Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  refine
    { toFun := fun u => ⟨fun i j => (u i j).val, ?_⟩
      invFun := fun u i j => ⟨u.1 i j, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_range.mpr (u i j).isLt
  · have hi := Fintype.mem_piFinset.mp u.2 i
    exact Finset.mem_range.mp (Fintype.mem_piFinset.mp hi j)
  · intro u
    funext i
    funext j
    apply Fin.ext
    rfl
  · intro u
    apply Subtype.ext
    funext i
    funext j
    rfl

theorem c_elim2_shiftAverage_eq_uniformFintypeAverage {α : Type u} [Fintype α]
    [DecidableEq α] (L : ℕ) (F : (α → Fin 2 → ℕ) → ℝ) :
    shiftAverage α L F =
      c_elim2_uniformFintypeAverage (fun u : α → Fin 2 → Fin L =>
        F (fun i j => (u i j).val)) := by
  classical
  let S : Finset (α → Fin 2 → ℕ) := Fintype.piFinset
    (fun _ : α => Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  let e := c_elim2_shiftRangeEquiv (α := α) L
  have hsum : (∑ u ∈ S, F u) =
      ∑ v : α → Fin 2 → Fin L, F (fun i j => (v i j).val) := by
    calc
      _ = ∑ u : {u : α → Fin 2 → ℕ // u ∈ S}, F u.1 := by
        simp [S, Finset.sum_attach]
      _ = _ := by
        symm
        exact Fintype.sum_equiv e
          (fun v => F (fun i j => (v i j).val))
          (fun u => F u.1) (by intro v; rfl)
  have hcard : Fintype.card (α → Fin 2 → Fin L) = L ^ (2 * Fintype.card α) := by
    calc
      Fintype.card (α → Fin 2 → Fin L) =
          (Fintype.card (Fin 2 → Fin L)) ^ Fintype.card α := by simp
      _ = (L ^ 2) ^ Fintype.card α := by simp
      _ = L ^ (2 * Fintype.card α) :=
        (pow_mul L 2 (Fintype.card α)).symm
  have hcardR : (Fintype.card (α → Fin 2 → Fin L) : ℝ) =
      (L : ℝ) ^ (2 * Fintype.card α) := by exact_mod_cast hcard
  unfold shiftAverage c_elim2_uniformFintypeAverage
  rw [hsum, hcardR]

noncomputable def c_elim2_shiftCoordPartitionEquiv {α : Type u}
    [DecidableEq α] (E : Finset α) :
    (α × Fin 2) ≃ c_elim2_ShiftCoord E ⊕ {i : α // i ∉ E} := by
  classical
  let f : (α × Fin 2) → c_elim2_ShiftCoord E ⊕ {i : α // i ∉ E} :=
    fun x => if hx : x.2.val = 0 ∨ x.1 ∈ E then
      Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x.1, fun hE => hx (Or.inr hE)⟩
  let g : c_elim2_ShiftCoord E ⊕ {i : α // i ∉ E} → α × Fin 2 :=
    fun y => match y with
      | Sum.inl c => c.val
      | Sum.inr i => (i.val, 1)
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    by_cases hx : x.2.val = 0 ∨ x.1 ∈ E
    · dsimp only [f]
      rw [dif_pos hx]
    · have hval : x.2.val = 1 := by omega
      have hxE : x.1 ∉ E := by
        intro hE
        exact hx (Or.inr hE)
      dsimp only [f]
      rw [dif_neg hx]
      dsimp only [g]
      change (x.1, 1) = x
      apply Prod.ext
      · rfl
      · exact Fin.ext hval.symm
  · intro y
    cases y with
    | inl c =>
        change f c.val = Sum.inl c
        dsimp only [f]
        rw [dif_pos c.property]
    | inr i => simp [f, g, i.property]

noncomputable def c_elim2_shiftAssignmentPartitionEquiv {α : Type u}
    [Fintype α] [DecidableEq α] (E : Finset α) (L : ℕ) :
    (α → Fin 2 → Fin L) ≃
      (c_elim2_ShiftCoord E → Fin L) × ({i : α // i ∉ E} → Fin L) := by
  let eCurry : (α → Fin 2 → Fin L) ≃ (α × Fin 2 → Fin L) :=
    { toFun := fun f x => f x.1 x.2
      invFun := fun f i j => f (i, j)
      left_inv := by intro f; funext i j; rfl
      right_inv := by intro f; funext x; cases x; rfl }
  exact eCurry.trans
    ((Equiv.arrowCongr (c_elim2_shiftCoordPartitionEquiv E)
      (Equiv.refl (Fin L))).trans
      (Equiv.sumArrowEquivProdArrow (c_elim2_ShiftCoord E)
        {i : α // i ∉ E} (Fin L)))

theorem c_elim2_uniformFintypeAverage_equiv {α β : Type*} [Fintype α]
    [Fintype β] (e : α ≃ β) (F : α → ℝ) :
    c_elim2_uniformFintypeAverage F =
      c_elim2_uniformFintypeAverage (fun b => F (e.symm b)) := by
  classical
  unfold c_elim2_uniformFintypeAverage
  have hsum : (∑ a, F a) = ∑ b, F (e.symm b) := by
    exact Fintype.sum_equiv e F (fun b => F (e.symm b)) (by intro a; simp)
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  rw [hsum, hcard]

theorem c_elim2_uniformFintypeAverage_depends_on_state {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Nonempty β]
    (e : γ ≃ α × β) (F : γ → ℝ) (G : α → ℝ)
    (hF : ∀ x, F x = G (e x).1) :
    c_elim2_uniformFintypeAverage F = c_elim2_uniformFintypeAverage G := by
  classical
  rw [c_elim2_uniformFintypeAverage_equiv e F,
    c_elim2_uniformFintypeAverage_prod]
  apply congrArg c_elim2_uniformFintypeAverage
  funext a
  simp [hF, Equiv.apply_symm_apply, c_elim2_uniformFintypeAverage_const]

theorem c_elim2_shiftAverage_eq_shiftStateAverage_of_depends
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (L : ℕ)
    (hL : 0 < L) (F : (α → Fin 2 → ℕ) → ℝ)
    (G : (c_elim2_ShiftCoord E → Fin L) → ℝ)
    (hF : ∀ u : α → Fin 2 → Fin L,
      F (fun i j => (u i j).val) =
        G (c_elim2_shiftAssignmentPartitionEquiv E L u).1) :
    shiftAverage α L F = c_elim2_shiftStateAverage E L G := by
  classical
  let e := c_elim2_shiftAssignmentPartitionEquiv E L
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI : Nonempty ({i : α // i ∉ E} → Fin L) := ⟨fun _ => ⟨0, hL⟩⟩
  rw [c_elim2_shiftAverage_eq_uniformFintypeAverage]
  change c_elim2_uniformFintypeAverage
      (fun u : α → Fin 2 → Fin L => F (fun i j => (u i j).val)) =
    c_elim2_uniformFintypeAverage G
  exact c_elim2_uniformFintypeAverage_depends_on_state e _ G hF

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

theorem c_elim2_boxState_insert_endpoint {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β)
    (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxStateIntegrand D (insert R E) b
      (c_elim2_boxEndpointAssignment E R hR (D.shiftLength b) o t₀ t₁) =
    c_elim2_boxWeightRowFactor D E R b
      (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀) *
      ∏ bit : Fin 2, c_elim2_boxWithoutActiveRow D E R b
        (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
          (c_elim2_boxEndpointChoice t₀ t₁ bit)) := by
  classical
  let oldState (bit : Fin 2) : c_elim2_ShiftCoord E → Fin (D.shiftLength b) :=
    c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o
      (c_elim2_boxEndpointChoice t₀ t₁ bit)
  let T (bit : Fin 2) := c_elim2_boxTargetProduct D E b (oldState bit)
  let A (bit : Fin 2) := c_elim2_boxOtherActiveProduct D E R b (oldState bit)
  let Q (bit : Fin 2) := c_elim2_boxRetainedProduct D E b (oldState bit)
  let Ω := c_elim2_boxWeightRowFactor D E R b
    (c_elim2_boxOldEndpointAssignment E R (D.shiftLength b) o t₀)
  have hTA : (∏ bit : Fin 2, T bit) * (∏ bit : Fin 2, A bit) =
      ∏ bit : Fin 2, T bit * A bit := by
    exact (Finset.prod_mul_distrib (s := Finset.univ) (f := T) (g := A)).symm
  have hAQ : (∏ bit : Fin 2, T bit * A bit) * (∏ bit : Fin 2, Q bit) =
      ∏ bit : Fin 2, (T bit * A bit) * Q bit := by
    exact (Finset.prod_mul_distrib (s := Finset.univ)
      (f := fun bit => T bit * A bit) (g := Q)).symm
  unfold c_elim2_boxStateIntegrand
  rw [c_elim2_boxTargetProduct_insert_endpoint,
    c_elim2_boxActiveProduct_insert_endpoint,
    c_elim2_boxRetainedProduct_insert_endpoint]
  calc
    (∏ bit : Fin 2, T bit) * (∏ bit : Fin 2, A bit) *
        (Ω * ∏ bit : Fin 2, Q bit) =
      Ω * ((∏ bit : Fin 2, T bit) * (∏ bit : Fin 2, A bit) *
        (∏ bit : Fin 2, Q bit)) := by ring
    _ = Ω * ((∏ bit : Fin 2, T bit * A bit) *
        (∏ bit : Fin 2, Q bit)) := by rw [hTA]
    _ = Ω * ∏ bit : Fin 2, (T bit * A bit) * Q bit := by
      rw [hAQ]
    _ = Ω * ∏ bit : Fin 2, T bit * A bit * Q bit := by
      congr 1
    _ = Ω * ∏ bit : Fin 2, c_elim2_boxWithoutActiveRow D E R b (oldState bit) := by
      congr 1

theorem c_elim2_boxShiftValue_split_outside {α : Type u} [Fintype α]
    [DecidableEq α]
    (E : Finset α) (R i : α) (hiR : i ≠ R) (L : ℕ)
    (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L) (ω : α → Fin 2) :
    c_elim2_boxShiftValue E
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₀)) ω i =
    c_elim2_boxShiftValue E
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₁)) ω i := by
  classical
  by_cases hiE : i ∈ E
  · let c : c_elim2_ShiftCoord E := ⟨(i, ω i), Or.inr hiE⟩
    have hc : c.val ≠ (R, 0) := by
      intro heq
      exact hiR (congrArg Prod.fst heq)
    have h₀ :
        (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₀) c =
          o ⟨c, hc⟩ :=
      c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except E R L o t₀ ⟨c, hc⟩
    have h₁ :
        (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₁) c =
          o ⟨c, hc⟩ :=
      c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except E R L o t₁ ⟨c, hc⟩
    simp [c_elim2_boxShiftValue, hiE, c, h₀, h₁]
  · let c : c_elim2_ShiftCoord E := ⟨(i, 0), Or.inl rfl⟩
    have hc : c.val ≠ (R, 0) := by
      intro heq
      exact hiR (congrArg Prod.fst heq)
    have h₀ :
        (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₀) c =
          o ⟨c, hc⟩ :=
      c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except E R L o t₀ ⟨c, hc⟩
    have h₁ :
        (c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₁) c =
          o ⟨c, hc⟩ :=
      c_elim2_shiftCoordAssignmentSplitEquiv_symm_apply_except E R L o t₁ ⟨c, hc⟩
    simp [c_elim2_boxShiftValue, hiE, c, h₀, h₁]

theorem c_elim2_boxRowArgument_split_outside {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (b : β) (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) (ω : α → Fin 2) :
    c_elim2_boxRowArgument D E b R
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₀)) ω =
    c_elim2_boxRowArgument D E b R
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₁)) ω := by
  unfold c_elim2_boxRowArgument
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hiR : i ≠ R := (Finset.mem_erase.mp hi).1
  rw [c_elim2_boxShiftValue_split_outside E R i hiR (D.shiftLength b) o t₀ t₁ ω]

theorem c_elim2_boxActiveRowFactor_split_outside {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (b : β) (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxActiveRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₀)) =
    c_elim2_boxActiveRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₁)) := by
  unfold c_elim2_boxActiveRowFactor
  apply Fintype.prod_congr
  intro ω
  rw [c_elim2_boxRowArgument_split_outside D E R b o t₀ t₁
    (c_elim2_boxBranchFull E ω)]

theorem c_elim2_boxWeightRowFactor_split_outside {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (b : β) (o : c_elim2_ShiftOutside E R (D.shiftLength b))
    (t₀ t₁ : Fin (D.shiftLength b)) :
    c_elim2_boxWeightRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₀)) =
    c_elim2_boxWeightRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t₁)) := by
  unfold c_elim2_boxWeightRowFactor
  apply Fintype.prod_congr
  intro ω
  rw [c_elim2_boxRowArgument_split_outside D E R b o t₀ t₁
    (c_elim2_boxBranchFull E ω)]

noncomputable def c_elim2_boxCurrentStateIntegrand {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (b : β) (H₀ : c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (H : c_elim2_ShiftOutside E R (D.shiftLength b) →
      Fin (D.shiftLength b) → ℝ)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) : ℝ := by
  classical
  let e := c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)
  exact H₀ (e u).1 * c_elim2_uniformFintypeAverage (H (e u).1)

noncomputable def c_elim2_boxNextStateIntegrand {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β)
    (Ω : c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (H : c_elim2_ShiftOutside E R (D.shiftLength b) →
      Fin (D.shiftLength b) → ℝ)
    (u : c_elim2_ShiftCoord (insert R E) → Fin (D.shiftLength b)) : ℝ := by
  classical
  let (v, t₁) := c_elim2_shiftStateInsertEquiv E R hR (D.shiftLength b) u
  let (o, t₀) := c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b) v
  exact Ω o * H o t₀ * H o t₁

theorem c_elim2_boxStateAverage_eq_current {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β) (tBase : Fin (D.shiftLength b))
    (H₀ : c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (H : c_elim2_ShiftOutside E R (D.shiftLength b) →
      Fin (D.shiftLength b) → ℝ)
    (hH₀ : ∀ o, H₀ o = c_elim2_boxActiveRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, tBase)))
    (hH : ∀ o t, H o t = c_elim2_boxWithoutActiveRow D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t))) :
    c_elim2_shiftStateAverage E (D.shiftLength b)
      (c_elim2_boxCurrentStateIntegrand D E R b H₀ H) =
    c_elim2_shiftStateAverage E (D.shiftLength b)
      (c_elim2_boxStateIntegrand D E b) := by
  classical
  let L := D.shiftLength b
  letI : Nonempty (Fin L) := ⟨tBase⟩
  rw [c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L),
    c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L)]
  apply congrArg (fun F : c_elim2_ShiftOutside E R L → ℝ =>
    c_elim2_uniformFintypeAverage F)
  funext o
  calc
    c_elim2_uniformFintypeAverage (fun t : Fin L =>
        c_elim2_boxCurrentStateIntegrand D E R b H₀ H
          ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t))) =
      c_elim2_uniformFintypeAverage (fun t : Fin L =>
        H₀ o * c_elim2_uniformFintypeAverage (H o)) := by
          apply congrArg (fun F : Fin L → ℝ => c_elim2_uniformFintypeAverage F)
          funext t
          simp [c_elim2_boxCurrentStateIntegrand, L, Equiv.apply_symm_apply]
    _ = H₀ o * c_elim2_uniformFintypeAverage (H o) :=
          c_elim2_uniformFintypeAverage_const _
    _ = c_elim2_uniformFintypeAverage (fun t : Fin L => H₀ o * H o t) :=
          (c_elim2_uniformFintypeAverage_const_mul (H₀ o) (H o)).symm
    _ = c_elim2_uniformFintypeAverage (fun t : Fin L =>
        c_elim2_boxActiveRowFactor D E R b
            ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t)) *
          c_elim2_boxWithoutActiveRow D E R b
            ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t))) := by
          apply congrArg (fun F : Fin L → ℝ => c_elim2_uniformFintypeAverage F)
          funext t
          rw [← c_elim2_boxActiveRowFactor_split_outside D E R b o tBase t]
          rw [← hH₀ o, ← hH o t]
    _ = c_elim2_uniformFintypeAverage (fun t : Fin L =>
        c_elim2_boxStateIntegrand D E b
          ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t))) := by
          apply congrArg (fun F : Fin L → ℝ => c_elim2_uniformFintypeAverage F)
          funext t
          rw [← c_elim2_boxState_factor_active D E R hR b
            ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t))]

theorem c_elim2_boxStateAverage_eq_next {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (hR : R ∉ E) (b : β) (tBase : Fin (D.shiftLength b))
    (Ω : c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (H : c_elim2_ShiftOutside E R (D.shiftLength b) →
      Fin (D.shiftLength b) → ℝ)
    (hΩ : ∀ o, Ω o = c_elim2_boxWeightRowFactor D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, tBase)))
    (hH : ∀ o t, H o t = c_elim2_boxWithoutActiveRow D E R b
      ((c_elim2_shiftCoordAssignmentSplitEquiv E R (D.shiftLength b)).symm (o, t))) :
    c_elim2_shiftStateAverage (insert R E) (D.shiftLength b)
      (c_elim2_boxNextStateIntegrand D E R hR b Ω H) =
    c_elim2_shiftStateAverage (insert R E) (D.shiftLength b)
      (c_elim2_boxStateIntegrand D (insert R E) b) := by
  classical
  let L := D.shiftLength b
  have hpoint (o : c_elim2_ShiftOutside E R L) (t₀ t₁ : Fin L) :
      c_elim2_boxStateIntegrand D (insert R E) b
        (c_elim2_boxEndpointAssignment E R hR L o t₀ t₁) =
      Ω o * H o t₀ * H o t₁ := by
    rw [c_elim2_boxState_insert_endpoint]
    have hΩ' : c_elim2_boxWeightRowFactor D E R b
        (c_elim2_boxOldEndpointAssignment E R L o t₀) = Ω o := by
      change c_elim2_boxWeightRowFactor D E R b
        ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, t₀)) = Ω o
      calc
        _ = c_elim2_boxWeightRowFactor D E R b
              ((c_elim2_shiftCoordAssignmentSplitEquiv E R L).symm (o, tBase)) :=
                (c_elim2_boxWeightRowFactor_split_outside D E R b o tBase t₀).symm
        _ = Ω o := (hΩ o).symm
    rw [hΩ']
    rw [Fin.prod_univ_two]
    simp [hH, c_elim2_boxEndpointChoice, c_elim2_boxOldEndpointAssignment, L]
    ring
  have hInsNext := c_elim2_shiftStateAverage_insert
    (E := E) (R := R) (hR := hR) (L := L)
    (F := c_elim2_boxNextStateIntegrand D E R hR b Ω H)
  have hInsState := c_elim2_shiftStateAverage_insert
    (E := E) (R := R) (hR := hR) (L := L)
    (F := c_elim2_boxStateIntegrand D (insert R E) b)
  rw [hInsNext, hInsState]
  rw [c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L),
    c_elim2_shiftStateAverage_split (E := E) (R := R) (L := L)]
  apply congrArg (fun F : c_elim2_ShiftOutside E R L → ℝ =>
    c_elim2_uniformFintypeAverage F)
  funext o
  apply congrArg (fun F : Fin L → ℝ => c_elim2_uniformFintypeAverage F)
  funext t₀
  apply congrArg (fun F : Fin L → ℝ => c_elim2_uniformFintypeAverage F)
  funext t₁
  simpa [c_elim2_boxNextStateIntegrand, c_elim2_boxEndpointAssignment,
    Equiv.apply_symm_apply, L] using
    (hpoint o t₀ t₁).symm

theorem c_elim2_abs_prod_le_of_nonneg {α : Type u} [DecidableEq α] (s : Finset α)
    (f g : α → ℝ) (hg : ∀ a ∈ s, 0 ≤ g a)
    (hfg : ∀ a ∈ s, |f a| ≤ g a) :
    |∏ a ∈ s, f a| ≤ ∏ a ∈ s, g a := by
  rw [Finset.abs_prod]
  suffices h : ∀ s : Finset α, (∀ a ∈ s, 0 ≤ g a) →
      (∀ a ∈ s, |f a| ≤ g a) → (∏ a ∈ s, |f a|) ≤ ∏ a ∈ s, g a by
    exact h s hg hfg
  intro s
  induction s using Finset.induction_on with
  | empty => intro; simp
  | @insert a s ha ih =>
      intro hg hfg
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hrestNonneg : ∀ x ∈ s, 0 ≤ g x := by
        intro x hx
        exact hg x (Finset.mem_insert_of_mem hx)
      have hrestBound : ∀ x ∈ s, |f x| ≤ g x := by
        intro x hx
        exact hfg x (Finset.mem_insert_of_mem hx)
      have hprodAbs : 0 ≤ ∏ x ∈ s, |f x| :=
        Finset.prod_nonneg (fun x hx => abs_nonneg (f x))
      have hprodWeight : 0 ≤ ∏ x ∈ s, g x := Finset.prod_nonneg hrestNonneg
      exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
        (ih hrestNonneg hrestBound) hprodAbs
        (hg a (Finset.mem_insert_self a s))

theorem c_elim2_boxActiveRowFactor_abs_le_weightRowFactor {α β : Type u}
    [Fintype α] [DecidableEq α] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b))
    (hweight : ∀ ω : c_elim2_BoxBranch E,
      0 ≤ D.rowWeight R b
        (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω)))
    (hbound : ∀ ω : c_elim2_BoxBranch E,
      |D.rowFunction R b
        (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω))| ≤
      D.rowWeight R b
        (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω))) :
    |c_elim2_boxActiveRowFactor D E R b u| ≤
      c_elim2_boxWeightRowFactor D E R b u := by
  classical
  unfold c_elim2_boxActiveRowFactor c_elim2_boxWeightRowFactor
  apply c_elim2_abs_prod_le_of_nonneg Finset.univ
  · intro ω hω
    exact hweight ω
  · intro ω hω
    exact hbound ω

theorem c_elim2_boxWeightRowFactor_nonneg {α β : Type u} [Fintype α]
    [DecidableEq α] (D : c_elim2_AdditiveBoxData α β) (E : Finset α)
    (R : α) (b : β) (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b))
    (hweight : ∀ ω : c_elim2_BoxBranch E,
      0 ≤ D.rowWeight R b
        (c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω))) :
    0 ≤ c_elim2_boxWeightRowFactor D E R b u := by
  classical
  unfold c_elim2_boxWeightRowFactor
  exact Finset.prod_nonneg (fun ω hω => hweight ω)

theorem c_elim2_boxWeightedShiftStateStep {α β : Type u} [Fintype α]
    [DecidableEq α] [Fintype β] (D : c_elim2_AdditiveBoxData α β)
    (E : Finset α) (R : α) (hR : R ∉ E) (μ : β → ℝ)
    (H₀ : ∀ b, c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (Ω : ∀ b, c_elim2_ShiftOutside E R (D.shiftLength b) → ℝ)
    (H : ∀ b, c_elim2_ShiftOutside E R (D.shiftLength b) →
      Fin (D.shiftLength b) → ℝ)
    (hL : ∀ b, 0 < D.shiftLength b)
    (hμ : ∀ b, 0 ≤ μ b) (hΩ : ∀ b o, 0 ≤ Ω b o)
    (h₀ : ∀ b o, |H₀ b o| ≤ Ω b o)
    (hCS : ∀ {γ : Type u} (μ Ω H₀ H₁ : γ → ℝ)
      (hμ : ∀ x, 0 ≤ μ x) (hΩ : ∀ x, 0 ≤ Ω x)
      (h₀ : ∀ x, |H₀ x| ≤ Ω x)
      (hΩs : Summable (fun x => μ x * Ω x))
      (h₁s : Summable (fun x => μ x * (Ω x * H₁ x ^ 2))),
      |∑' x, μ x * (H₀ x * H₁ x)| ^ 2 ≤
        (∑' x, μ x * Ω x) * ∑' x, μ x * (Ω x * H₁ x ^ 2))
    (hCurrent : ∀ b,
      c_elim2_shiftStateAverage E (D.shiftLength b)
        (c_elim2_csCurrentIntegrand E R (fun b => D.shiftLength b) H₀ H b) =
      c_elim2_shiftStateAverage E (D.shiftLength b)
        (c_elim2_boxStateIntegrand D E b))
    (hNext : ∀ b,
      c_elim2_shiftStateAverage (insert R E) (D.shiftLength b)
        (c_elim2_csNextIntegrand E R hR (fun b => D.shiftLength b) Ω H b) =
      c_elim2_shiftStateAverage (insert R E) (D.shiftLength b)
        (c_elim2_boxStateIntegrand D (insert R E) b)) :
    |c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_boxStateIntegrand D E)| ^ 2 ≤
      c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_csWeightIntegrand E R (fun b => D.shiftLength b) Ω) *
      c_elim2_jointStateAverage (insert R E) μ (fun b => D.shiftLength b)
        (c_elim2_boxStateIntegrand D (insert R E)) := by
  classical
  have hcurrent :
      c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_csCurrentIntegrand E R (fun b => D.shiftLength b) H₀ H) =
      c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_boxStateIntegrand D E) := by
    unfold c_elim2_jointStateAverage
    apply Finset.sum_congr rfl
    intro b hb
    rw [hCurrent b]
  have hnext :
      c_elim2_jointStateAverage (insert R E) μ (fun b => D.shiftLength b)
        (c_elim2_csNextIntegrand E R hR (fun b => D.shiftLength b) Ω H) =
      c_elim2_jointStateAverage (insert R E) μ (fun b => D.shiftLength b)
        (c_elim2_boxStateIntegrand D (insert R E)) := by
    unfold c_elim2_jointStateAverage
    apply Finset.sum_congr rfl
    intro b hb
    rw [hNext b]
  calc
    |c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_boxStateIntegrand D E)| ^ 2 =
      |c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
        (c_elim2_csCurrentIntegrand E R (fun b => D.shiftLength b) H₀ H)| ^ 2 := by
          rw [hcurrent]
    _ ≤ c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
          (c_elim2_csWeightIntegrand E R (fun b => D.shiftLength b) Ω) *
        c_elim2_jointStateAverage (insert R E) μ (fun b => D.shiftLength b)
          (c_elim2_csNextIntegrand E R hR (fun b => D.shiftLength b) Ω H) :=
            c_elim2_weightedShiftStateStep E R hR μ
              (fun b => D.shiftLength b) hL H₀ Ω H hμ hΩ h₀ hCS
    _ = c_elim2_jointStateAverage E μ (fun b => D.shiftLength b)
          (c_elim2_csWeightIntegrand E R (fun b => D.shiftLength b) Ω) *
        c_elim2_jointStateAverage (insert R E) μ (fun b => D.shiftLength b)
          (c_elim2_boxStateIntegrand D (insert R E)) := by
            rw [hnext]

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

theorem c_elim2_boxWeightRowFactor_le_boxRetainedProduct
    {α β : Type u} [Fintype α] [DecidableEq α]
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α)
    (hR : R ∉ E) (b : β) (v : α → Fin 2 → Fin (D.shiftLength b))
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b))
    (hu : ∀ c, u c = v c.val.1 c.val.2)
    (hweight : ∀ (I : {i : α // i ∈ (Finset.univ : Finset α)})
      (η : c_elim2_BoxRetainedBranch (Finset.univ : Finset α) I.1),
      1 ≤ D.rowWeight I.1 b
        (c_elim2_boxRowArgument D Finset.univ b I.1
          (fun c : c_elim2_ShiftCoord (Finset.univ : Finset α) =>
            v c.val.1 c.val.2)
          (c_elim2_boxRetainedBranchFull (Finset.univ : Finset α) I.1 η))) :
    c_elim2_boxWeightRowFactor D E R b u ≤
      c_elim2_boxRetainedProduct D Finset.univ b
        (fun c : c_elim2_ShiftCoord (Finset.univ : Finset α) => v c.val.1 c.val.2) := by
  classical
  let fullU : c_elim2_ShiftCoord (Finset.univ : Finset α) → Fin (D.shiftLength b) :=
    fun c => v c.val.1 c.val.2
  let FullBranch := c_elim2_BoxRetainedBranch (Finset.univ : Finset α) R
  let extend : c_elim2_BoxBranch E → FullBranch := fun ω => fun η =>
    if hη : η.1 ∈ E then ω ⟨η.1, hη⟩ else 0
  have hinj : Function.Injective extend := by
    intro ω ω' h
    funext i
    have hiR : i.1 ≠ R := by
      intro heq
      exact hR (heq ▸ i.2)
    let η : {j : α // j ∈ Finset.univ.erase R} :=
      ⟨i.1, Finset.mem_erase.mpr ⟨hiR, Finset.mem_univ _⟩⟩
    have hev := congrFun h η
    have hmem : η.1 ∈ E := by simpa [η] using i.2
    have hsub : (⟨η.1, hmem⟩ : {j : α // j ∈ E}) = i := by
      apply Subtype.ext
      rfl
    simpa [extend, hmem, hsub] using hev
  have harg (ω : c_elim2_BoxBranch E) :
      c_elim2_boxRowArgument D E b R u (c_elim2_boxBranchFull E ω) =
        c_elim2_boxRowArgument D Finset.univ b R fullU
          (c_elim2_boxRetainedBranchFull Finset.univ R (extend ω)) := by
    unfold c_elim2_boxRowArgument
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hiR : i ≠ R := (Finset.mem_erase.mp hi).1
    by_cases hiE : i ∈ E
    · let bit : Fin 2 := c_elim2_boxBranchFull E ω i
      let cP : c_elim2_ShiftCoord E := ⟨(i, bit), Or.inr hiE⟩
      let cF : c_elim2_ShiftCoord Finset.univ :=
        ⟨(i, bit), Or.inr (Finset.mem_univ i)⟩
      have hbit : bit = c_elim2_boxRetainedBranchFull Finset.univ R (extend ω) i := by
        simp [bit, c_elim2_boxBranchFull, c_elim2_boxRetainedBranchFull,
          extend, hiE, hiR]
      have hcoord : u cP = fullU cF := by
        have hu' := hu cP
        simpa [cP, cF, fullU, hbit] using hu'
      have hshiftP : c_elim2_boxShiftValue E u (c_elim2_boxBranchFull E ω) i =
          (u cP).val := by
        simp [c_elim2_boxShiftValue, cP, bit, hiE]
      have hshiftF : c_elim2_boxShiftValue Finset.univ fullU
          (c_elim2_boxRetainedBranchFull Finset.univ R (extend ω)) i =
          (fullU cF).val := by
        simp [c_elim2_boxShiftValue, cF, bit, hbit]
      rw [hshiftP, hshiftF, hcoord]
    · have hbit : c_elim2_boxBranchFull E ω i = 0 := by
        simp [c_elim2_boxBranchFull, hiE]
      have hbitFull : c_elim2_boxRetainedBranchFull Finset.univ R (extend ω) i = 0 := by
        simp [c_elim2_boxRetainedBranchFull, c_elim2_boxBranchFull, extend, hiE]
      let cP : c_elim2_ShiftCoord E := ⟨(i, 0), Or.inl rfl⟩
      let cF : c_elim2_ShiftCoord Finset.univ :=
        ⟨(i, 0), Or.inr (Finset.mem_univ i)⟩
      have hcoord : u cP = fullU cF := by
        have hu' := hu cP
        simpa [cP, cF, fullU] using hu'
      have hshiftP : c_elim2_boxShiftValue E u (c_elim2_boxBranchFull E ω) i =
          (u cP).val := by
        simp [c_elim2_boxShiftValue, cP, hiE]
      have hshiftF : c_elim2_boxShiftValue Finset.univ fullU
          (c_elim2_boxRetainedBranchFull Finset.univ R (extend ω)) i =
          (fullU cF).val := by
        simp [c_elim2_boxShiftValue, cF, hbitFull]
      rw [hshiftP, hshiftF, hcoord]
  let rowFactor : FullBranch → ℝ := fun η =>
    D.rowWeight R b
      (c_elim2_boxRowArgument D Finset.univ b R fullU
        (c_elim2_boxRetainedBranchFull Finset.univ R η))
  have hrowSub : c_elim2_boxWeightRowFactor D E R b u ≤
      ∏ η : FullBranch, rowFactor η := by
    unfold c_elim2_boxWeightRowFactor
    exact Finset.prod_le_prod_of_injOn₀
      (f := fun ω : c_elim2_BoxBranch E =>
        D.rowWeight R b (c_elim2_boxRowArgument D E b R u
          (c_elim2_boxBranchFull E ω)))
      (g := rowFactor) (s := Finset.univ) (t := Finset.univ)
      extend hinj.injOn
      (by intro ω hω; exact Finset.mem_univ _)
      (by
        intro ω hω
        rw [harg ω])
      (by
        intro ω hω
        rw [harg ω]
        exact le_trans (by positivity) (hweight ⟨R, Finset.mem_univ _⟩ (extend ω)))
      (by
        intro η hη hηnot
        exact hweight ⟨R, Finset.mem_univ _⟩ η)
  have hrowFactorLe : (∏ η : FullBranch, rowFactor η) ≤
      c_elim2_boxRetainedProduct D Finset.univ b fullU := by
    let Rows := {i : α // i ∈ (Finset.univ : Finset α)}
    let rowFactorAll : Rows → ℝ := fun I =>
      ∏ η : c_elim2_BoxRetainedBranch (Finset.univ : Finset α) I.1,
        D.rowWeight I.1 b
          (c_elim2_boxRowArgument D Finset.univ b I.1 fullU
            (c_elim2_boxRetainedBranchFull Finset.univ I.1 η))
    have hrowOne (I : Rows) : 1 ≤ rowFactorAll I := by
      dsimp [rowFactorAll]
      calc
        1 = ∏ η : c_elim2_BoxRetainedBranch Finset.univ I.1, (1 : ℝ) := by simp
        _ ≤ ∏ η : c_elim2_BoxRetainedBranch Finset.univ I.1,
            D.rowWeight I.1 b
              (c_elim2_boxRowArgument D Finset.univ b I.1 fullU
                (c_elim2_boxRetainedBranchFull Finset.univ I.1 η)) := by
          apply Finset.prod_le_prod₀
          · intro η hη
            norm_num
          · intro η hη
            exact hweight I η
    let Rset : Finset Rows := Finset.univ.filter fun I => I.1 = R
    have hRset : Rset = {⟨R, Finset.mem_univ R⟩} := by
      ext I
      constructor
      · intro h
        simp only [Finset.mem_singleton]
        apply Subtype.ext
        exact (Finset.mem_filter.mp h).2
      · intro h
        simp only [Finset.mem_singleton] at h
        rw [h]
        simp [Rset]
    have hsubset : Rset ⊆ (Finset.univ : Finset Rows) := Finset.filter_subset _ _
    have hprod : (∏ I ∈ Rset, rowFactorAll I) ≤ ∏ I, rowFactorAll I := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hsubset
      · intro I hI
        exact (zero_le_one.trans (hrowOne I))
      · intro I hI hInot
        exact hrowOne I
    have hsingle : (∏ I ∈ Rset, rowFactorAll I) =
        ∏ η : FullBranch, rowFactor η := by
      rw [hRset]
      simp only [Finset.prod_singleton]
      change (∏ η : FullBranch, rowFactor η) = ∏ η : FullBranch, rowFactor η
      rfl
    have hwhole : (∏ I, rowFactorAll I) =
        c_elim2_boxRetainedProduct D Finset.univ b fullU := by
      unfold c_elim2_boxRetainedProduct
      change (∏ I : Rows, rowFactorAll I) =
        ∏ I : Rows, ∏ η : c_elim2_BoxRetainedBranch Finset.univ I.1,
          D.rowWeight I.1 b
            (c_elim2_boxRowArgument D Finset.univ b I.1 fullU
              (c_elim2_boxRetainedBranchFull Finset.univ I.1 η))
      apply Fintype.prod_congr
      intro I
      rfl
    calc
      (∏ η : FullBranch, rowFactor η) = ∏ I ∈ Rset, rowFactorAll I := hsingle.symm
      _ ≤ ∏ I, rowFactorAll I := hprod
      _ = c_elim2_boxRetainedProduct D Finset.univ b fullU := hwhole
  calc
    c_elim2_boxWeightRowFactor D E R b u ≤
        ∏ η : FullBranch, rowFactor η := hrowSub
    _ ≤ c_elim2_boxRetainedProduct D Finset.univ b fullU := hrowFactorLe

theorem c_elim2_boxShiftValue_eq_fullAssignment
    {α : Type u} [DecidableEq α] (E : Finset α) {L : ℕ}
    (u : c_elim2_ShiftCoord E → Fin L) (v : α → Fin 2 → Fin L)
    (ω : α → Fin 2) (i : α)
    (hu : ∀ c, u c = v c.val.1 c.val.2)
    (hω : i ∉ E → ω i = 0) :
    c_elim2_boxShiftValue E u ω i = (v i (ω i)).val := by
  by_cases hi : i ∈ E
  · simp only [c_elim2_boxShiftValue, dif_pos hi]
    exact congrArg Fin.val (hu ⟨(i, ω i), Or.inr hi⟩)
  · have hω0 : ω i = 0 := hω hi
    simp only [c_elim2_boxShiftValue, dif_neg hi]
    rw [hω0]
    exact congrArg Fin.val (hu ⟨(i, 0), Or.inl rfl⟩)

theorem c_elim2_boxTargetArgument_eq_targetVertex
    {m q r : ℕ} {Sh : RowShape m q r} {β : Type}
    (D : c_elim2_AdditiveBoxData (NonTarget Sh) β)
    (E : Finset (NonTarget Sh)) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b))
    (v : NonTarget Sh → Fin 2 → Fin (D.shiftLength b))
    (ω : c_elim2_BoxBranch E) (c : Fin m → ℚ)
    (p : Fin q → ℕ) (z : Fin m → ℚ) (Mp : ℕ)
    (hbase : D.targetBase b = rowForm c (Sh.row Sh.star) p z)
    (hcoef : ∀ i, (D.targetCoefficient b i : ℚ) = (Mp : ℚ))
    (hu : ∀ c, u c = v c.val.1 c.val.2) :
    c_elim2_boxTargetArgument D E b u ω =
      targetVertex c Sh p Mp z
        (fun i j => (v i j).val) (c_elim2_boxBranchFull E ω) := by
  classical
  unfold c_elim2_boxTargetArgument targetVertex
  rw [hbase]
  calc
    rowForm c (Sh.row Sh.star) p z +
        ∑ i, (D.targetCoefficient b i : ℚ) *
          (c_elim2_boxShiftValue E u (c_elim2_boxBranchFull E ω) i : ℚ) =
      rowForm c (Sh.row Sh.star) p z +
        ∑ i, (Mp : ℚ) * ((v i (c_elim2_boxBranchFull E ω i)).val : ℚ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoef i]
          congr 1
          exact congrArg (fun n : ℕ => (n : ℚ))
            (c_elim2_boxShiftValue_eq_fullAssignment E u v
              (c_elim2_boxBranchFull E ω) i hu
              (by intro hi; simp [c_elim2_boxBranchFull, hi]))
    _ = rowForm c (Sh.row Sh.star) p z +
        (Mp : ℚ) * ∑ i, ((v i (c_elim2_boxBranchFull E ω i)).val : ℚ) := by
          rw [Finset.mul_sum]
    _ = _ := rfl

theorem c_elim2_boxRowArgument_linear
    {α β : Type u} [Fintype α] [DecidableEq α] {m q : ℕ}
    (D : c_elim2_AdditiveBoxData α β) (E : Finset α) (R : α) (b : β)
    (u : c_elim2_ShiftCoord E → Fin (D.shiftLength b)) (ω : α → Fin 2)
    (c : Fin m → ℚ) (T : RowTemplate m q) (p : Fin q → ℕ)
    (z : Fin m → ℚ) (v : α → Fin m → ℚ)
    (hbase : D.rowBase R b = rowForm c T p z)
    (hcoef : ∀ i, i ≠ R → (D.rowCoefficient R i b : ℚ) = rowForm c T p (v i)) :
    c_elim2_boxRowArgument D E b R u ω =
      rowForm c T p (fun k => z k + ∑ i ∈ Finset.univ.erase R,
        (c_elim2_boxShiftValue E u ω i : ℚ) * v i k) := by
  classical
  unfold c_elim2_boxRowArgument
  rw [hbase]
  have hsum :
      (∑ i ∈ Finset.univ.erase R,
        (D.rowCoefficient R i b : ℚ) *
          (c_elim2_boxShiftValue E u ω i : ℚ)) =
      ∑ i ∈ Finset.univ.erase R,
        (c_elim2_boxShiftValue E u ω i : ℚ) * rowForm c T p (v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoef i (Finset.mem_erase.mp hi).1]
    ring
  rw [hsum]
  exact (c_elim2_rowForm_finset_sum c T p z (Finset.univ.erase R)
    (fun i => (c_elim2_boxShiftValue E u ω i : ℚ)) v).symm

theorem c_elim2_iterate_box_cauchy {α : Type u} [Fintype α] [DecidableEq α]
    (F : Finset α → ℝ) (C : ℝ) (hC : 0 < C)
    (hstep : ∀ (E : Finset α), E ⊆ Finset.univ → ∀ R, R ∈ Finset.univ → R ∉ E →
      |F E| ^ 2 ≤ C * F (insert R E))
    (hnonneg : ∀ E : Finset α, E.Nonempty → 0 ≤ F E) :
    |F ∅| ^ (2 ^ Fintype.card α) ≤
      C ^ (2 ^ Fintype.card α - 1) * |F Finset.univ| := by
  classical
  have hiter : ∀ n, ∀ E : Finset α,
      (Finset.univ \ E).card = n → E ⊆ Finset.univ →
      |F E| ^ (2 ^ n) ≤ C ^ (2 ^ n - 1) * |F Finset.univ| := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro E hcard hE
        by_cases hn0 : n = 0
        · have hcard0 := hcard
          subst n
          have hEeq : E = Finset.univ := by
            ext x
            constructor
            · intro hx
              exact Finset.mem_univ x
            · intro hx
              by_contra hxE
              have hpos : 0 < (Finset.univ \ E).card :=
                Finset.card_pos.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxE⟩⟩
              rw [hcard0] at hpos
              omega
          simp [hEeq]
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have hremNonempty : (Finset.univ \ E).Nonempty := by
            by_contra h
            have hempty : Finset.univ \ E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
            rw [hempty] at hcard
            simp at hcard
            omega
          obtain ⟨R, hRrem⟩ := hremNonempty
          have hRmem : R ∈ Finset.univ := (Finset.mem_sdiff.mp hRrem).1
          have hRnotE : R ∉ E := (Finset.mem_sdiff.mp hRrem).2
          let E' := insert R E
          have hE' : E' ⊆ Finset.univ := by
            intro x hx
            rcases Finset.mem_insert.mp hx with hxR | hxE
            · simpa [hxR]
            · exact hE hxE
          have hcard' : (Finset.univ \ E').card = n - 1 := by
            dsimp [E']
            rw [Finset.sdiff_insert, Finset.card_erase_of_mem hRrem, hcard]
          have hnext := ih (n - 1) (by omega) E' hcard' hE'
          have hFnext : 0 ≤ F E' :=
            hnonneg E' ⟨R, Finset.mem_insert_self R E⟩
          have hstepN := hstep E hE R hRmem hRnotE
          let k : ℕ := 2 ^ (n - 1)
          have hpowIndex : 2 ^ n = 2 * k := by
            dsimp [k]
            calc
              2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
              _ = 2 ^ (n - 1) * 2 := by rw [Nat.pow_succ]
              _ = 2 * 2 ^ (n - 1) := by omega
          have hpower := pow_le_pow_left₀ (sq_nonneg (|F E|)) hstepN k
          have hnextAbs : |F E'| = F E' := abs_of_nonneg hFnext
          rw [hnextAbs] at hnext
          calc
            |F E| ^ (2 ^ n) = (|F E| ^ 2) ^ k := by
              rw [hpowIndex, pow_mul]
            _ ≤ (C * F E') ^ k := hpower
            _ = C ^ k * F E' ^ k := by rw [mul_pow]
            _ ≤ C ^ k * (C ^ (k - 1) * |F Finset.univ|) := by
              exact mul_le_mul_of_nonneg_left hnext (by positivity)
            _ = C ^ (2 ^ n - 1) * |F Finset.univ| := by
              rw [← mul_assoc, ← pow_add]
              congr 2
              dsimp [k]
              omega
  have hmain := hiter (Fintype.card α) ∅ (by simp) (Finset.empty_subset _)
  simpa using hmain

theorem c_elim2_uniformFintypeAverage_mono {α : Type*} [Fintype α]
    (f g : α → ℝ) (h : ∀ x, f x ≤ g x) :
    c_elim2_uniformFintypeAverage f ≤ c_elim2_uniformFintypeAverage g := by
  unfold c_elim2_uniformFintypeAverage
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun x hx => h x)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem c_elim2_shiftStateAverage_le_fullUniformAverage
    {α : Type u} [Fintype α] [DecidableEq α] (E : Finset α) (L : ℕ)
    (hL : 0 < L) (G : (c_elim2_ShiftCoord E → Fin L) → ℝ)
    (F : (α → Fin 2 → Fin L) → ℝ)
    (hpoint : ∀ u : α → Fin 2 → Fin L,
      G (c_elim2_shiftAssignmentPartitionEquiv E L u).1 ≤ F u) :
    c_elim2_shiftStateAverage E L G ≤ c_elim2_uniformFintypeAverage F := by
  classical
  let e := c_elim2_shiftAssignmentPartitionEquiv E L
  let Outside := {i : α // i ∉ E} → Fin L
  letI : Fintype Outside := inferInstance
  letI : Nonempty Outside := ⟨fun _ => ⟨0, hL⟩⟩
  have hdep : c_elim2_uniformFintypeAverage (fun u => G (e u).1) =
      c_elim2_uniformFintypeAverage G :=
    c_elim2_uniformFintypeAverage_depends_on_state e
      (fun u => G (e u).1) G (by intro u; rfl)
  change c_elim2_uniformFintypeAverage G ≤ c_elim2_uniformFintypeAverage F
  calc
    c_elim2_uniformFintypeAverage G =
        c_elim2_uniformFintypeAverage (fun u => G (e u).1) := hdep.symm
    _ ≤ c_elim2_uniformFintypeAverage F :=
      c_elim2_uniformFintypeAverage_mono _ _ hpoint

theorem c_elim2_normalized_product_measure {P Z : Type*} [Fintype P] [Fintype Z]
    (a b : P → ℝ) (c : Z → ℝ) (prob : ℝ)
    (hP : (∑ p, a p * b p) = prob) (hZ : (∑ z, c z) = 1)
    (hprob : 0 < prob) :
    ∑ x : P × Z, prob⁻¹ * (a x.1 * b x.1 * c x.2) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner (p : P) :
      (∑ z : Z, prob⁻¹ * (a p * b p * c z)) =
        prob⁻¹ * (a p * b p * ∑ z : Z, c z) := by
    calc
      _ = ∑ z : Z, (prob⁻¹ * (a p * b p)) * c z := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = (prob⁻¹ * (a p * b p)) * ∑ z : Z, c z := by
        rw [← Finset.mul_sum]
      _ = _ := by ring
  calc
    (∑ p : P, ∑ z : Z, prob⁻¹ * (a p * b p * c z)) =
        ∑ p : P, prob⁻¹ * (a p * b p * ∑ z : Z, c z) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hinner p
    _ = prob⁻¹ * (∑ p : P, a p * b p) * (∑ z : Z, c z) := by
      calc
        _ = ∑ p : P, (prob⁻¹ * (∑ z : Z, c z)) * (a p * b p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = (prob⁻¹ * (∑ z : Z, c z)) * ∑ p : P, a p * b p := by
          rw [← Finset.mul_sum]
        _ = _ := by ring
    _ = 1 := by rw [hP, hZ]; field_simp

theorem c_elim2_arithmeticL1_product_le_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : ι → ℤ → ℝ) (S : Finset ℤ)
    (hμzero : ∀ i z, z ∉ S → μ i z = 0)
    (hνzero : ∀ i z, z ∉ S → ν i z = 0)
    (hμnonneg : ∀ i z, 0 ≤ μ i z) (hνnonneg : ∀ i z, 0 ≤ ν i z)
    (hμmass : ∀ i, ∑' z : ℤ, μ i z = 1)
    (hνmass : ∀ i, ∑' z : ℤ, ν i z = 1) :
    arithmeticL1 (fun x : ι → ℤ => ∏ i, μ i (x i))
      (fun x => ∏ i, ν i (x i)) ≤ ∑ i, arithmeticL1 (μ i) (ν i) := by
  classical
  let β := {z : ℤ // z ∈ S}
  letI : Fintype β := Finset.Subtype.fintype S
  let μ' : ι → β → ℝ := fun i z => μ i z.1
  let ν' : ι → β → ℝ := fun i z => ν i z.1
  have hμmass' (i : ι) : ∑ z : β, μ' i z = 1 := by
    have hsum : ∑ z ∈ S, μ i z = 1 := by
      rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
        (f := μ i) (s := S) (fun z hz => hμzero i z hz)]
      exact hμmass i
    change ∑ z ∈ S.attach, μ i z.1 = 1
    rw [Finset.sum_attach]
    exact hsum
  have hνmass' (i : ι) : ∑ z : β, ν' i z = 1 := by
    have hsum : ∑ z ∈ S, ν i z = 1 := by
      rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
        (f := ν i) (s := S) (fun z hz => hνzero i z hz)]
      exact hνmass i
    change ∑ z ∈ S.attach, ν i z.1 = 1
    rw [Finset.sum_attach]
    exact hsum
  have hμabs (i : ι) : ∑ z : β, |μ' i z| = 1 := by
    calc
      _ = ∑ z : β, μ' i z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [abs_of_nonneg (hμnonneg i z.1)]
      _ = 1 := hμmass' i
  have hνabs (i : ι) : ∑ z : β, |ν' i z| = 1 := by
    calc
      _ = ∑ z : β, ν' i z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [abs_of_nonneg (hνnonneg i z.1)]
      _ = 1 := hνmass' i
  let μProd : (ι → β) → ℝ := fun x => ∏ i, μ' i (x i)
  let νProd : (ι → β) → ℝ := fun x => ∏ i, ν' i (x i)
  let raw : (ι → β) → (ι → ℤ) := fun x i => (x i).1
  have hrawInj : Function.Injective raw := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  let Sprod : Finset (ι → ℤ) := Fintype.piFinset fun _ : ι => S
  have hμprodZero : ∀ x, x ∉ Sprod → (∏ i, μ i (x i)) = 0 := by
    intro x hx
    have hnotall : ¬ ∀ i : ι, x i ∈ S := by
      intro hall
      apply hx
      change x ∈ Fintype.piFinset (fun _ : ι => S)
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hμzero i (x i) hi)
  have hνprodZero : ∀ x, x ∉ Sprod → (∏ i, ν i (x i)) = 0 := by
    intro x hx
    have hnotall : ¬ ∀ i : ι, x i ∈ S := by
      intro hall
      apply hx
      change x ∈ Fintype.piFinset (fun _ : ι => S)
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hνzero i (x i) hi)
  have hL1tsum : arithmeticL1 (fun x : ι → ℤ => ∏ i, μ i (x i))
      (fun x => ∏ i, ν i (x i)) =
      ∑ x ∈ Sprod, |(∏ i, μ i (x i)) - ∏ i, ν i (x i)| := by
    unfold arithmeticL1
    rw [tsum_eq_sum (L := SummationFilter.unconditional (ι → ℤ))
      (s := Sprod) (f := fun x : ι → ℤ =>
        |(∏ i, μ i (x i)) - ∏ i, ν i (x i)|)
      (by intro x hx; simp [hμprodZero x hx, hνprodZero x hx])]
  have hImage : Finset.univ.image raw = Sprod := by
    ext x
    rw [Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    change (∃ y : ι → β, raw y = x) ↔
      x ∈ Fintype.piFinset (fun _ : ι => S)
    rw [Fintype.mem_piFinset]
    constructor
    · rintro ⟨y, rfl⟩
      intro i
      exact (y i).property
    · intro hx
      refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
      funext i
      rfl
  have hL1finite :
      (∑ x ∈ Sprod, |(∏ i, μ i (x i)) - ∏ i, ν i (x i)|) =
        finiteL1 μProd νProd := by
    rw [← hImage]
    rw [Finset.sum_image (s := (Finset.univ : Finset (ι → β)))
      (f := fun x : ι → ℤ => |(∏ i, μ i (x i)) - ∏ i, ν i (x i)|)
      (g := raw)
      hrawInj.injOn]
    simp [finiteL1, μProd, νProd, μ', ν', raw]
  have hprodTV := FromArithmetic.finite_product_l1_telescoping μ' ν'
  calc
    arithmeticL1 (fun x : ι → ℤ => ∏ i, μ i (x i))
        (fun x => ∏ i, ν i (x i)) = finiteL1 μProd νProd := hL1tsum.trans hL1finite
    _ ≤ ∑ i, finiteL1 (μ' i) (ν' i) *
          ∏ j ∈ Finset.univ.erase i,
            max (∑ z : β, |μ' j z|) (∑ z : β, |ν' j z|) := hprodTV
    _ = ∑ i, finiteL1 (μ' i) (ν' i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hμabs, hνabs]
    _ = ∑ i, arithmeticL1 (μ i) (ν i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hattach : (∑ z : β, |μ i z.1 - ν i z.1|) =
          ∑ z ∈ S, |μ i z - ν i z| := by
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach S (fun z => |μ i z - ν i z|))
      have htsum : arithmeticL1 (μ i) (ν i) =
          ∑ z ∈ S, |μ i z - ν i z| := by
        unfold arithmeticL1
        rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
          (s := S) (f := fun z : ℤ => |μ i z - ν i z|)
          (by intro z hz; simp [hμzero i z hz, hνzero i z hz])]
      unfold finiteL1
      exact hattach.trans htsum.symm

theorem c_elim2_arithmeticL1_test_bound
    {α : Type*} [DecidableEq α] (μ ν F : α → ℝ) (S : Finset α)
    (B : ℝ) (hB : 0 ≤ B)
    (hμzero : ∀ x, x ∉ S → μ x = 0)
    (hνzero : ∀ x, x ∉ S → ν x = 0)
    (hF : ∀ x, |F x| ≤ B) :
    |∑' x, (μ x - ν x) * F x| ≤ B * arithmeticL1 μ ν := by
  classical
  have hexpect : ∑' x, (μ x - ν x) * F x =
      ∑ x ∈ S, (μ x - ν x) * F x := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional α) (s := S)
      (f := fun x => (μ x - ν x) * F x)
      (by intro x hx; simp [hμzero x hx, hνzero x hx])]
  have hL1 : arithmeticL1 μ ν = ∑ x ∈ S, |μ x - ν x| := by
    unfold arithmeticL1
    rw [tsum_eq_sum (L := SummationFilter.unconditional α) (s := S)
      (f := fun x => |μ x - ν x|)
      (by intro x hx; simp [hμzero x hx, hνzero x hx])]
  rw [hexpect, hL1]
  calc
    |∑ x ∈ S, (μ x - ν x) * F x| ≤
        ∑ x ∈ S, |(μ x - ν x) * F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, B * |μ x - ν x| := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        |μ x - ν x| * |F x| ≤ |μ x - ν x| * B :=
          mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
        _ = B * |μ x - ν x| := mul_comm _ _
    _ = B * ∑ x ∈ S, |μ x - ν x| := by rw [Finset.mul_sum]

theorem c_elim2_productTranslation_expectation_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → ℤ → ℝ)
    (h : ι → ℤ) (S : Finset ℤ) (F : (ι → ℤ) → ℝ) (B ε : ℝ)
    (hB : 0 ≤ B)
    (hμzero : ∀ i z, z ∉ S → μ i z = 0)
    (hνzero : ∀ i z, z ∉ S → translatedLaw (μ i) (h i) z = 0)
    (hμnonneg : ∀ i z, 0 ≤ μ i z)
    (hμmass : ∀ i, ∑' z : ℤ, μ i z = 1)
    (hcoordL1 : ∀ i, arithmeticL1 (translatedLaw (μ i) (h i)) (μ i) ≤ ε)
    (hF : ∀ z, |F z| ≤ B) :
    |(∑' z : ι → ℤ, (∏ i, μ i (z i)) * F (fun i => z i + h i)) -
      ∑' z, (∏ i, μ i (z i)) * F z| ≤ B * (Fintype.card ι : ℝ) * ε := by
  classical
  let ν : ι → ℤ → ℝ := fun i z => translatedLaw (μ i) (h i) z
  let μProd : (ι → ℤ) → ℝ := fun z => ∏ i, μ i (z i)
  let νProd : (ι → ℤ) → ℝ := fun z => ∏ i, ν i (z i)
  let Sprod : Finset (ι → ℤ) := Fintype.piFinset fun _ : ι => S
  have hνnonneg : ∀ i z, 0 ≤ ν i z := by
    intro i z
    exact hμnonneg i (z - h i)
  have hνmass : ∀ i, ∑' z : ℤ, ν i z = 1 := by
    intro i
    calc
      _ = ∑' z : ℤ, μ i (Equiv.addRight (-h i) z) := by
        simp [ν, translatedLaw, Equiv.coe_addRight, sub_eq_add_neg]
      _ = ∑' z : ℤ, μ i z := (Equiv.addRight (-h i)).tsum_eq (fun z => μ i z)
      _ = 1 := hμmass i
  have hμprodZero : ∀ z, z ∉ Sprod → μProd z = 0 := by
    intro z hz
    have hnotall : ¬ ∀ i : ι, z i ∈ S := by
      intro hall
      apply hz
      change z ∈ Fintype.piFinset (fun _ : ι => S)
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hμzero i (z i) hi)
  have hνprodZero : ∀ z, z ∉ Sprod → νProd z = 0 := by
    intro z hz
    have hnotall : ¬ ∀ i : ι, z i ∈ S := by
      intro hall
      apply hz
      change z ∈ Fintype.piFinset (fun _ : ι => S)
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hνzero i (z i) hi)
  have hchange :
      (∑' z : ι → ℤ, μProd z * F (fun i => z i + h i)) =
        ∑' z : ι → ℤ, νProd z * F z := by
    calc
      _ = ∑' z : ι → ℤ, νProd (fun i => z i + h i) *
          F (fun i => z i + h i) := by
        apply tsum_congr
        intro z
        simp [μProd, νProd, ν, translatedLaw, sub_add_cancel]
      _ = _ := (Equiv.addRight h).tsum_eq (fun z => νProd z * F z)
  have hprodTV := c_elim2_arithmeticL1_product_le_sum ν μ S
    (by intro i z hz; exact hνzero i z hz)
    hμzero hνnonneg hμnonneg hνmass hμmass
  have hprodTVle : arithmeticL1 νProd μProd ≤ (Fintype.card ι : ℝ) * ε := by
    calc
      arithmeticL1 νProd μProd ≤ ∑ i, arithmeticL1 (ν i) (μ i) := hprodTV
      _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i hi => hcoordL1 i)
      _ = (Fintype.card ι : ℝ) * ε := by simp
  have htest := c_elim2_arithmeticL1_test_bound νProd μProd F Sprod B hB
    hνprodZero hμprodZero hF
  have hsumνF : ∑' z : ι → ℤ, νProd z * F z =
      ∑ z ∈ Sprod, νProd z * F z := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional (ι → ℤ)) (s := Sprod)
      (f := fun z => νProd z * F z)
      (by intro z hz; simp [hνprodZero z hz])]
  have hsumμF : ∑' z : ι → ℤ, μProd z * F z =
      ∑ z ∈ Sprod, μProd z * F z := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional (ι → ℤ)) (s := Sprod)
      (f := fun z => μProd z * F z)
      (by intro z hz; simp [hμprodZero z hz])]
  have hdiff :
      (∑' z : ι → ℤ, νProd z * F z) - ∑' z, μProd z * F z =
        ∑' z : ι → ℤ, (νProd z - μProd z) * F z := by
    rw [hsumνF, hsumμF]
    rw [tsum_eq_sum (L := SummationFilter.unconditional (ι → ℤ)) (s := Sprod)
      (f := fun z => (νProd z - μProd z) * F z)
      (by intro z hz; simp [hνprodZero z hz, hμprodZero z hz])]
    calc
      _ = ∑ z ∈ Sprod, (νProd z * F z - μProd z * F z) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ z ∈ Sprod, (νProd z - μProd z) * F z := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
  calc
    _ = |(∑' z : ι → ℤ, νProd z * F z) - ∑' z, μProd z * F z| := by rw [hchange]
    _ = |∑' z : ι → ℤ, (νProd z - μProd z) * F z| := by rw [hdiff]
    _ ≤ B * arithmeticL1 νProd μProd := htest
    _ ≤ B * ((Fintype.card ι : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hprodTVle hB
    _ = B * (Fintype.card ι : ℝ) * ε := by ring

theorem c_elim2_microcellDominates_mono {A B S : ℕ → ℝ}
    (hle : ∀ᶠ n in atTop, A n ≤ B n)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hA : OAI.MicrocellScale.Dominates A S) :
    OAI.MicrocellScale.Dominates B S := by
  intro C hC
  apply tendsto_atTop_mono' atTop _ (hA C hC)
  filter_upwards [hle, hS] with n hn hSn
  exact div_le_div_of_nonneg_right hn
    (le_of_lt (Real.rpow_pos_of_pos hSn C))

theorem c_elim2_microcellDominates_trans {A B S : ℕ → ℝ}
    (hAB : OAI.MicrocellScale.Dominates A B)
    (hBS : OAI.MicrocellScale.Dominates B S)
    (hS : ∀ᶠ n in atTop, 0 < S n) :
    OAI.MicrocellScale.Dominates A S := by
  intro C hC
  have habT : Tendsto (fun n => A n / B n) atTop atTop := by
    simpa [pow_one] using hAB 1 (by norm_num)
  have hbsT := hBS C hC
  apply tendsto_atTop_mono' atTop _ hbsT
  filter_upwards [habT.eventually_ge_atTop (1 : ℝ),
    hbsT.eventually_ge_atTop (1 : ℝ), hS] with n hab hbs hSn
  have hpow : 0 < (S n) ^ C := Real.rpow_pos_of_pos hSn C
  have hBpos : 0 < B n := by
    have hmul : (S n) ^ C ≤ B n := by simpa using (le_div_iff₀ hpow).mp hbs
    exact lt_of_lt_of_le hpow hmul
  have hfactor : A n / (S n) ^ C = (A n / B n) * (B n / (S n) ^ C) := by
    field_simp [ne_of_gt hBpos, ne_of_gt hpow]
  rw [hfactor]
  calc
    B n / (S n) ^ C ≤ (A n / B n) * (B n / (S n) ^ C) := by
      simpa using (mul_le_mul_of_nonneg_right hab
        (le_of_lt (lt_of_lt_of_le zero_lt_one hbs)))
    _ = _ := rfl

theorem c_elim2_microcellDominates_of_le_denominator {A S T : ℕ → ℝ}
    (hST : ∀ᶠ n in atTop, S n ≤ T n)
    (hSpos : ∀ᶠ n in atTop, 0 < S n)
    (hTpos : ∀ᶠ n in atTop, 0 < T n)
    (hA : OAI.MicrocellScale.Dominates A T) :
    OAI.MicrocellScale.Dominates A S := by
  intro C hC
  have hAt := hA C hC
  apply tendsto_atTop_mono' atTop _ hAt
  filter_upwards [hST, hSpos, hTpos, hAt.eventually_ge_atTop (1 : ℝ)]
    with n hSTn hSn hTn hRatio
  have hSpow : 0 < (S n : ℝ) ^ C := Real.rpow_pos_of_pos hSn C
  have hTpow : 0 < (T n : ℝ) ^ C := Real.rpow_pos_of_pos hTn C
  have hSleT : (S n : ℝ) ^ C ≤ (T n : ℝ) ^ C :=
    Real.rpow_le_rpow (by linarith) (by exact_mod_cast hSTn) (by positivity)
  have hApos : 0 ≤ A n := by
    have hmul : (T n : ℝ) ^ C ≤ A n := by simpa using (le_div_iff₀ hTpow).mp hRatio
    exact le_trans (le_of_lt hTpow) hmul
  exact (div_le_div_iff₀ hTpow hSpow).2
    (mul_le_mul_of_nonneg_left hSleT hApos)

theorem c_elim2_microcellDominates_of_eventually_le_pow
    {A T U : ℕ → ℝ} (q : ℕ)
    (hA : OAI.MicrocellScale.Dominates A T)
    (hT : ∀ᶠ n in atTop, 2 ≤ T n)
    (hUpos : ∀ᶠ n in atTop, 0 < U n)
    (hU : ∀ᶠ n in atTop, U n ≤ T n ^ (q + 3 : ℕ)) :
    OAI.MicrocellScale.Dominates A U := by
  intro C hC
  let C' : ℝ := C * ((q + 3 : ℕ) : ℝ)
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hAt := hA C' hC'
  apply tendsto_atTop_mono' atTop _ hAt
  filter_upwards [hAt.eventually_ge_atTop (1 : ℝ), hT, hUpos, hU]
    with n hAdiv hTn hUnpos hUn
  have hTpos : 0 < T n := by linarith
  have hUreal : U n ≤ T n ^ ((q + 3 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact hUn
  have hUto : (U n) ^ C ≤ (T n) ^ C' := by
    calc
      _ ≤ ((T n) ^ ((q + 3 : ℕ) : ℝ)) ^ C :=
        Real.rpow_le_rpow (le_of_lt hUnpos) hUreal hC.le
      _ = (T n) ^ C' := by
        dsimp [C']
        simpa [mul_comm] using
          (Real.rpow_mul (le_of_lt hTpos) ((q + 3 : ℕ) : ℝ) C).symm
  have hDen : 0 < (T n) ^ C' := Real.rpow_pos_of_pos hTpos C'
  have hApos : 0 ≤ A n := by
    have hmul : (T n) ^ C' ≤ A n := by simpa using (le_div_iff₀ hDen).mp hAdiv
    exact le_trans (le_of_lt (Real.rpow_pos_of_pos hTpos C')) hmul
  have hcomp : A n / (T n) ^ C' ≤ A n / (U n) ^ C := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hDen (Real.rpow_pos_of_pos hUnpos C)).2 hUto) hApos
  exact hcomp

theorem c_elim2_harmonicCutoffLogCondition {X W : ℕ}
    (hW : 0 < W) (hX : 4 * W ≤ X) :
    Real.log (X : ℝ) > (W : ℝ) / X := by
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have h := Real.self_sub_one_lt_mul_log (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢ <;> nlinarith
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have hmul := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at hmul ⊢
    nlinarith [hmul, hlog2]
  have hXfour : 4 ≤ X := by omega
  have hlogX : 1 < Real.log (X : ℝ) := by
    apply lt_of_lt_of_le hlog4
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hXfour)
  have hXpos : (0 : ℝ) < X := by positivity
  have hratio : (W : ℝ) / X ≤ 1 / 4 := by
    rw [div_le_iff₀ hXpos]
    have hcast : (4 : ℝ) * W ≤ X := by exact_mod_cast hX
    nlinarith
  linarith

theorem c_elim2_masterScaleV_ge_primorial {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (l : Fin n) :
    primorial (N + 1) ≤ FromArithmetic.masterScaleV A N l := by
  have hW : primorial (N + 1) ≤ A.M N := A.Wle N
  unfold FromArithmetic.masterScaleV
  omega

theorem c_elim2_logCutoff_dominates_gapScale {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (j : Fin m) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (S.core.parameters.X N (C.block j).1 : ℝ))
      (fun N => (S.core.parameters.H N C.gap : ℝ)) := by
  have hgapLe : ∀ N, (S.core.parameters.H N C.gap : ℝ) ≤
      (S.core.parameters.H N (C.block j).1 : ℝ) := by
    intro N
    have hdiv := S.gapStage.earlier_gaps_divide N C.gap (C.block j).1
      (C.pivots_after_gap j)
    exact_mod_cast Nat.le_of_dvd (S.core.parameters.Hpos N (C.block j).1) hdiv
  have hGpos : ∀ N, 0 < (S.core.parameters.H N C.gap : ℝ) := by
    intro N
    exact_mod_cast S.core.parameters.Hpos N C.gap
  have hPivotPos : ∀ N, 0 < (S.core.parameters.H N (C.block j).1 : ℝ) := by
    intro N
    exact_mod_cast S.core.parameters.Hpos N (C.block j).1
  exact c_elim2_microcellDominates_of_le_denominator
    (Filter.Eventually.of_forall hgapLe)
    (Filter.Eventually.of_forall hGpos)
    (Filter.Eventually.of_forall hPivotPos)
    (S.gapStage.raw_cutoff_log_dominates_gap (C.block j).1)

theorem c_elim2_pivotTranslationError_superpolynomial
    {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (j : Fin m) (d B : ℕ) :
    SuperPolynomialSmall
      (fun N => FromArithmetic.harmonicTranslationUniformError
        (S.core.parameters.X N (C.block j).1) (primorial (N + 1))
        ((d + 1) * (S.core.parameters.H N C.gap + 1) *
          ((S.primeStage.pool N C.gap).upper +
            FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ B))
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) := by
  classical
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV S.core.parameters N C.gap
  let T : ℕ → ℕ := fun N => (S.primeStage.pool N C.gap).upper + V N
  let G : ℕ → ℕ := fun N => S.core.parameters.H N C.gap
  let Hshift : ℕ → ℕ := fun N => (d + 1) * (G N + 1) * T N ^ B
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let Kseq : ℕ → ℕ := fun _ => 1
  let X : ℕ → ℕ := fun N => S.core.parameters.X N (C.block j).1
  let U : ℕ → ℕ := fun N => 2 + W N + Kseq N + Hshift N + V N
  let Ulog : ℕ → ℕ := fun N => 2 + W N + Kseq N + V N
  have hV : ∀ N, 2 ≤ V N := by
    intro N
    dsimp [V, FromArithmetic.masterScaleV]
    omega
  have hWleV : ∀ N, W N ≤ V N := by
    intro N
    exact c_elim2_masterScaleV_ge_primorial S.core.parameters N C.gap
  have hT : ∀ N, 2 ≤ T N := by
    intro N
    have hVn := hV N
    dsimp [T]
    exact le_trans hVn
      (Nat.le_add_left (V N) (S.primeStage.pool N C.gap).upper)
  have hratio : Tendsto (fun N => (G N : ℝ) / (T N : ℝ)) atTop atTop := by
    simpa [G, T, pow_one] using S.gapStage.gap_dominates_pool_and_bound C.gap
      1 (by norm_num)
  have hGlarge : ∀ᶠ N in atTop, max (d + 1) 2 ≤ G N := by
    filter_upwards [hratio.eventually_ge_atTop (max (d + 1) 2 : ℝ)] with N hN
    have hTpos : 0 < (T N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (hT N))
    have hmul : (max (d + 1) 2 : ℝ) * (T N : ℝ) ≤ (G N : ℝ) :=
      (le_div_iff₀ hTpos).mp hN
    have hTlower : (1 : ℝ) ≤ (T N : ℝ) := by exact_mod_cast (Nat.le_trans (by norm_num) (hT N))
    have hD : (max (d + 1) 2 : ℝ) ≤ (G N : ℝ) := by nlinarith
    exact_mod_cast hD
  have hGgeT : ∀ᶠ N in atTop, T N ≤ G N := by
    filter_upwards [hratio.eventually_ge_atTop (1 : ℝ)] with N hN
    have hTpos : 0 < (T N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (hT N))
    have hmul : (1 : ℝ) * (T N : ℝ) ≤ (G N : ℝ) := (le_div_iff₀ hTpos).mp hN
    have hmul' : (T N : ℝ) ≤ (G N : ℝ) := by simpa using hmul
    exact_mod_cast hmul'
  have hGge2 : ∀ᶠ N in atTop, 2 ≤ G N := by
    filter_upwards [hGlarge] with N hN
    exact le_trans (by omega) hN
  have hGpos : ∀ᶠ N in atTop, 0 < (G N : ℝ) := by
    filter_upwards [hGge2] with N hN
    exact_mod_cast (by omega : 0 < G N)
  have hlogDomG := c_elim2_logCutoff_dominates_gapScale S C j
  have hlogleX : ∀ᶠ N in atTop, Real.log (X N : ℝ) ≤ (X N : ℝ) := by
    filter_upwards [] with N
    have hXpos : 0 < X N := by
      dsimp [X]
      have hcut := S.gapStage.valid_raw_cutoffs N (C.block j).1
      have hWpos := primorial_pos (N + 1)
      omega
    exact Real.log_le_self (by exact_mod_cast hXpos.le)
  have hXDomG : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ))
      (fun N => (G N : ℝ)) := by
    exact c_elim2_microcellDominates_mono hlogleX hGpos hlogDomG
  have hHshiftBound : ∀ᶠ N in atTop, Hshift N ≤ G N ^ (B + 3) := by
    filter_upwards [hGlarge, hGgeT] with N hGN hGT
    have hD : d + 1 ≤ G N := le_trans (le_max_left _ _) hGN
    have hG1 : G N + 1 ≤ 2 * G N := by omega
    have hG2 : 2 ≤ G N := le_trans (le_max_right _ _) hGN
    have hTpow : T N ^ B ≤ G N ^ B := Nat.pow_le_pow_left hGT B
    have hmult : (d + 1) * (G N + 1) * T N ^ B ≤
        G N * (2 * G N) * G N ^ B := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hD hG1) hTpow
    have hbase : G N * (2 * G N) * G N ^ B = 2 * G N ^ (B + 2) := by
      rw [Nat.pow_add]
      rw [Nat.pow_two]
      ring
    have hdouble : 2 * G N ^ (B + 2) ≤ G N ^ (B + 3) := by
      rw [Nat.pow_succ]
      calc
        2 * G N ^ (B + 2) = G N ^ (B + 2) * 2 := by omega
        _ ≤ G N ^ (B + 2) * G N := Nat.mul_le_mul_left _ hG2
    exact le_trans (hmult.trans_eq hbase) hdouble
  have hUle : ∀ᶠ N in atTop, (U N : ℝ) ≤ (G N : ℝ) ^ (B + 4 : ℕ) := by
    filter_upwards [hGlarge, hGgeT, hHshiftBound] with N hGN hGT hHB
    have hG : 2 ≤ G N := le_trans (by omega) hGN
    have hGsq : 4 ≤ G N ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ G N ^ 2 := Nat.pow_le_pow_left hG 2
    have hfour : 4 * G N ≤ G N ^ 3 := by
      calc
        4 * G N ≤ G N ^ 2 * G N := Nat.mul_le_mul_right _ hGsq
        _ = G N ^ 3 := (Nat.pow_succ (G N) 2).symm
    have hrest : 2 + W N + 1 + V N ≤ G N ^ 3 := by
      have hVleT : V N ≤ T N := by
        dsimp [T]
        exact Nat.le_add_left (V N) (S.primeStage.pool N C.gap).upper
      have hV' : V N ≤ G N := hVleT.trans hGT
      have hW : W N ≤ G N := (hWleV N).trans hV'
      have hsum : 2 + W N + 1 + V N ≤ 4 * G N := by omega
      exact hsum.trans hfour
    have hrestPow : 2 + W N + 1 + V N ≤ G N ^ (B + 3) := by
      exact le_trans hrest (Nat.pow_le_pow_right (by omega) (by omega))
    have hdouble : 2 * G N ^ (B + 3) ≤ G N ^ (B + 4) := by
      rw [Nat.pow_succ]
      calc
        2 * G N ^ (B + 3) = G N ^ (B + 3) * 2 := by omega
        _ ≤ G N ^ (B + 3) * G N := Nat.mul_le_mul_left _ hG
    have hUnat : U N ≤ G N ^ (B + 4) := by
      calc
        U N = (2 + W N + 1 + V N) + Hshift N := by
          dsimp [U, Kseq]
          ring
        _ ≤ G N ^ (B + 3) + G N ^ (B + 3) := Nat.add_le_add hrestPow hHB
        _ = 2 * G N ^ (B + 3) := by ring
        _ ≤ G N ^ (B + 4) := hdouble
    exact_mod_cast hUnat
  have hUlogle : ∀ᶠ N in atTop, (Ulog N : ℝ) ≤ (T N : ℝ) ^ (3 : ℕ) := by
    filter_upwards [] with N
    have hT2 := hT N
    have hTsq : 4 ≤ T N ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ T N ^ 2 := Nat.pow_le_pow_left hT2 2
    have hfour : 4 * T N ≤ T N ^ 3 := by
      calc
        4 * T N ≤ T N ^ 2 * T N := Nat.mul_le_mul_right _ hTsq
        _ = T N ^ 3 := (Nat.pow_succ (T N) 2).symm
    have hV' : V N ≤ T N := by
      dsimp [T]
      exact Nat.le_add_left (V N) (S.primeStage.pool N C.gap).upper
    have hW : W N ≤ T N := (hWleV N).trans hV'
    have hsum : 2 + W N + 1 + V N ≤ 4 * T N := by omega
    have hUnat : Ulog N ≤ T N ^ 3 := by
      dsimp [Ulog, Kseq]
      exact hsum.trans hfour
    exact_mod_cast hUnat
  have hUpos : ∀ᶠ N in atTop, 0 < (U N : ℝ) := by
    filter_upwards [] with N
    dsimp [U]
    positivity
  have hUlogpos : ∀ᶠ N in atTop, 0 < (Ulog N : ℝ) := by
    filter_upwards [] with N
    dsimp [Ulog]
    positivity
  have hXDomU : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ))
      (fun N => (U N : ℝ)) :=
    c_elim2_microcellDominates_of_eventually_le_pow (B + 1) hXDomG
      (by filter_upwards [hGge2] with N hN; exact_mod_cast hN)
      hUpos hUle
  have hGgeTreal : ∀ᶠ N in atTop, (T N : ℝ) ≤ (G N : ℝ) := by
    filter_upwards [hGgeT] with N hN
    exact_mod_cast hN
  have hTposreal : ∀ᶠ N in atTop, 0 < (T N : ℝ) := by
    filter_upwards [] with N
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (hT N))
  have hGdomT : OAI.MicrocellScale.Dominates (fun N => (G N : ℝ))
      (fun N => (T N : ℝ)) := by
    simpa [G, T] using S.gapStage.gap_dominates_pool_and_bound C.gap
  have hlogDomT := c_elim2_microcellDominates_trans hlogDomG hGdomT hTposreal
  have hlogDomUlog : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
      (fun N => (Ulog N : ℝ)) :=
    c_elim2_microcellDominates_of_eventually_le_pow 0 hlogDomT
      (Filter.Eventually.of_forall (fun N => by exact_mod_cast hT N))
      hUlogpos hUlogle
  let hSampleSeq : ℕ → ℕ := Hshift
  have hK : ∀ N, 1 ≤ Kseq N := by intro N; simp [Kseq]
  have hH : ∀ N, 1 ≤ hSampleSeq N := by
    intro N
    dsimp [hSampleSeq, Hshift]
    have hTN := hT N
    have hpow : 1 ≤ T N ^ B := Nat.one_le_pow B (T N) (by omega)
    have hA : 1 ≤ d + 1 := by omega
    have hG : 1 ≤ G N + 1 := by omega
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ (d + 1) * (G N + 1) * T N ^ B :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hG) hpow
  have hVpos : ∀ N, 1 ≤ V N := by intro N; exact le_trans (by omega) (hV N)
  have hW : ∀ N, W N = primorial (N + 1) := by intro N; rfl
  have hX2 : ∀ᶠ N in atTop, 2 ≤ X N := by
    filter_upwards [] with N
    dsimp [X]
    have hcut := S.gapStage.valid_raw_cutoffs N (C.block j).1
    have hWpos := primorial_pos (N + 1)
    omega
  have hden : ∀ᶠ N in atTop, Real.log (X N : ℝ) > (W N : ℝ) / X N := by
    filter_upwards [] with N
    dsimp [X, W]
    exact c_elim2_harmonicCutoffLogCondition (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block j).1)
  have hSampling := FromArithmetic.sampling_asymptotics W Kseq hSampleSeq V X
    hK hH hVpos hW hX2 hden
    (by simpa [U, W, Kseq, hSampleSeq, Nat.cast_add, Nat.cast_one, add_assoc] using hXDomU)
    (by simpa [Ulog, W, Kseq, Nat.cast_add, Nat.cast_one, add_assoc] using hlogDomUlog)
  simpa [V, W, X, T, G, Hshift, hSampleSeq,
    FromArithmetic.harmonicTranslationUniformError] using hSampling.2.1

end HindmanSumsProducts
