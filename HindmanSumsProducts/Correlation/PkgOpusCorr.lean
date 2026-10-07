import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgMask
import HindmanSumsProducts.Correlation.PkgPrime

/-! Helpers of lane `opus-corr` for weighted mask removal (04:135–308) and weighted additive
elimination (04:418–572). -/

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable
open FromArithmetic

/-! ## One mask-removal step and its iteration -/

/-- One step of the proof of Lemma `lem:mask-removal` (04:173–297), from a state with shape `Sh`
and masks `masks` to a state with one mask `U` fewer and two more prime slots. The new shape,
its tests and the constant depend only on `Sh`, `masks`, `U` and `J_*`; the inequality
`|𝒞|² ≤ C₁|𝒞'|+ε` holds eventually, uniformly over all valid states. -/
def opus_corr_MaskStep (m : ℕ) (Jstar : Finset (Fin m)) : Prop :=
  ∀ {q r : ℕ} (Sh : RowShape m q r), (Sh.row Sh.star).support = Jstar →
  ∀ (masks : Finset (Finset (Fin m))) (U : Finset (Fin m)), U ∈ masks →
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r') (tests : Finset (IntegerPolynomial (q + 2)))
      (C₁ : ℝ),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin (q + 2) ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ (st : MaskRemovalState m q r) (gstar : ℤ → ℝ),
          st.shape = Sh → st.masks = masks → st.Valid S C a N Jstar gstar →
          ∃ st' : MaskRemovalState m (q + 2) r',
            st'.shape = Sh' ∧ st'.masks = masks.erase U ∧ st'.Valid S C a N Jstar gstar ∧
            |st.correlation S C a N| ^ 2 ≤ C₁ * |st'.correlation S C a N| + ε

/-- `(x+e)² ≤ 2x²+2e²`, used to raise a step inequality to the next power. -/
theorem opus_corr_sq_add_le (x e : ℝ) : (x + e) ^ 2 ≤ 2 * x ^ 2 + 2 * e ^ 2 := by
  nlinarith [sq_nonneg (x - e)]

/-- Combining `X^{2^k} ≤ A y+e₁` and `y² ≤ B z+e₂` (all quantities nonnegative). -/
theorem opus_corr_power_step {X y z A B e₁ e₂ : ℝ} (k : ℕ) (hX : 0 ≤ X)
    (h₁ : X ^ (2 ^ k) ≤ A * y + e₁) (h₂ : y ^ 2 ≤ B * z + e₂) :
    X ^ (2 ^ (k + 1)) ≤ (2 * A ^ 2 * B) * z + (2 * A ^ 2 * e₂ + 2 * e₁ ^ 2) := by
  have hpow : X ^ (2 ^ (k + 1)) = (X ^ (2 ^ k)) ^ 2 := by
    rw [pow_succ, pow_mul]
  have hXk : 0 ≤ X ^ (2 ^ k) := pow_nonneg hX _
  have hsq : (X ^ (2 ^ k)) ^ 2 ≤ (A * y + e₁) ^ 2 :=
    pow_le_pow_left₀ hXk h₁ 2
  have h2 := opus_corr_sq_add_le (A * y) e₁
  have hA2 : 0 ≤ 2 * A ^ 2 := by positivity
  have h3 : 2 * (A * y) ^ 2 ≤ 2 * A ^ 2 * (B * z + e₂) := by
    rw [mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h₂ hA2
  rw [hpow]
  nlinarith

/-- Mask removal along a duplicate-free list of nonempty masks, from the initial state
(04:135–140): after removing the masks of `L`, the remaining masks are the others, the shape has
`2|L|` slots and at most `q_mask 2^{|L|}` rows, and `|𝒞|^{2^{|L|}} ≤ C|𝒞_L|+ε`. -/
theorem opus_corr_mask_iterate (m : ℕ) (Jstar : Finset (Fin m)) (hJ : 2 ≤ Jstar.card)
    (hstep : opus_corr_MaskStep m Jstar) (L : List (Finset (Fin m))) (hL : L.Nodup)
    (hLne : ∀ U ∈ L, U.Nonempty) :
    ∃ (q r : ℕ) (Sh : RowShape m q r) (tests : Finset (IntegerPolynomial q)) (Cm : ℝ),
      q = 2 * L.length ∧ r ≤ maskCount m * 2 ^ L.length ∧
      (Sh.row Sh.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < Cm ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ b g : Finset (Fin m) → ℤ → ℝ,
        FunctionsValid S.core.parameters C N b g →
        ∃ st : MaskRemovalState m q r, st.shape = Sh ∧
          st.masks = nonemptyMaskFinset m \ L.toFinset ∧
          st.Valid S C a N Jstar (g Jstar) ∧
          |maskedCorrelation S.core.parameters C a N b g| ^ (2 ^ L.length) ≤
            Cm * |st.correlation S C a N| + ε := by
  classical
  induction L with
  | nil =>
    refine ⟨0, maskCount m, initialMaskShape Jstar hJ, ∅, 1, by simp, by simp,
      initialMaskShape_star_support Jstar hJ, by simp, one_pos, ?_⟩
    intro K s Aset Dm S ι _ C a _ ε hε
    refine Filter.Eventually.of_forall fun N b g hv => ?_
    refine ⟨initialMaskRemovalState Jstar hJ b g, rfl, ?_,
      initialMaskRemovalState_valid S C a N Jstar hJ b g hv, ?_⟩
    · ext U
      simp [initialMaskRemovalState, nonemptyMaskFinset]
    · rw [initialMaskRemovalState_correlation]
      simp only [List.length_nil, pow_zero, pow_one, one_mul]
      linarith
  | cons U rest ih =>
    rcases List.nodup_cons.mp hL with ⟨hUrest, hrest⟩
    have hrestNe : ∀ V ∈ rest, V.Nonempty := fun V hV => hLne V (List.mem_cons_of_mem U hV)
    have hUne : U.Nonempty := hLne U (List.mem_cons_self)
    obtain ⟨q, r, Sh, tests, Cm, hq, hr, hStar, htests, hCm, hmain⟩ := ih hrest hrestNe
    have hUmem : U ∈ nonemptyMaskFinset m \ rest.toFinset := by
      simp [nonemptyMaskFinset, hUne, hUrest]
    obtain ⟨r', Sh', tests', C₁, hr', hStar', htests', hC₁, hstepMain⟩ :=
      hstep Sh hStar (nonemptyMaskFinset m \ rest.toFinset) U hUmem
    let emb : Fin q → Fin (q + 2) := Fin.castAdd 2
    have hemb : Function.Injective emb := Fin.castAdd_injective q 2
    let tests'' : Finset (IntegerPolynomial (q + 2)) :=
      tests' ∪ tests.image (MvPolynomial.rename emb)
    refine ⟨q + 2, r', Sh', tests'', 2 * Cm ^ 2 * C₁, ?_, ?_, hStar', ?_, by positivity, ?_⟩
    · simp [hq]
      ring
    · calc
        r' ≤ 2 * r := hr'
        _ ≤ 2 * (maskCount m * 2 ^ rest.length) := Nat.mul_le_mul_left 2 hr
        _ = maskCount m * 2 ^ (U :: rest).length := by
          simp only [List.length_cons, pow_succ]
          ring
    · intro P hP
      rcases Finset.mem_union.mp hP with hP' | hP'
      · exact htests' P hP'
      · obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP'
        intro hzero
        apply htests P₀ hP₀
        apply MvPolynomial.rename_injective emb hemb
        simpa using hzero
    · intro K s Aset Dm S ι hlisted C a ha ε hε
      let ιold : Fin q ↪ Fin s := ⟨fun i => ι (emb i), fun i j h => hemb (ι.injective h)⟩
      have hlistedOld : TestsListed Dm ιold tests := by
        intro P hP
        have hmem : MvPolynomial.rename emb P ∈ tests'' :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP)
        have h := hlisted _ hmem
        rw [MvPolynomial.rename_rename] at h
        exact h
      have hlistedNew : TestsListed Dm ι tests' := by
        intro P hP
        exact hlisted P (Finset.mem_union_left _ hP)
      let ε₁ : ℝ := min 1 (ε / 4)
      have hε₁ : 0 < ε₁ := lt_min one_pos (by positivity)
      let ε₂ : ℝ := ε / (4 * Cm ^ 2 + 1)
      have hε₂ : 0 < ε₂ := by positivity
      filter_upwards [hmain S ιold hlistedOld C a ha ε₁ hε₁,
        hstepMain S ι hlistedNew C a ha ε₂ hε₂] with N hN hNstep
      intro b g hv
      obtain ⟨st, hsh, hmasks, hvalid, hineq⟩ := hN b g hv
      obtain ⟨st', hsh', hmasks', hvalid', hineq'⟩ :=
        hNstep st (g Jstar) hsh hmasks hvalid
      refine ⟨st', hsh', ?_, hvalid', ?_⟩
      · rw [hmasks', List.toFinset_cons, Finset.sdiff_insert]
      · have hpow := opus_corr_power_step rest.length (abs_nonneg _) hineq hineq'
        have he₁ : ε₁ ≤ 1 := min_le_left _ _
        have he₁' : ε₁ ≤ ε / 4 := min_le_right _ _
        have hsq : ε₁ ^ 2 ≤ ε₁ := by nlinarith
        have hε₂' : 2 * Cm ^ 2 * ε₂ ≤ ε / 2 := by
          have hden : 0 < 4 * Cm ^ 2 + 1 := by positivity
          have : 2 * Cm ^ 2 * ε₂ = (2 * Cm ^ 2) * ε / (4 * Cm ^ 2 + 1) := by
            simp only [ε₂]; ring
          rw [this, div_le_iff₀ hden]
          nlinarith [sq_nonneg Cm]
        have hlen : (U :: rest).length = rest.length + 1 := rfl
        rw [hlen]
        linarith


/-! ## Balanced mask-removal step: generic averaging tools -/

section BalancedTools

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

theorem opus_corr_primePoolLaw_eq_zero (lo hi k : ℕ) (hk : k ∉ primePoolSupport lo hi) :
    primePoolLaw lo hi k = 0 := by
  by_contra hne
  have hcond : lo ≤ k ∧ k < hi ∧ k.Prime := by
    by_contra hnot
    exact hne (by simp [primePoolLaw, hnot])
  exact hk (by simp [primePoolSupport, Finset.mem_filter, Finset.mem_Ico, hcond])

theorem opus_corr_harmonicLaw_eq_zero (X W : ℕ) (z : ℤ) (hz : z ∉ harmonicLawSupport X W) :
    harmonicLaw X W z = 0 := by
  by_contra hne
  have hcond : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W := by
    by_contra hnot
    exact hne (by simp [harmonicLaw, hnot])
  have hnmem : z.toNat ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hcond.2.1, hcond.2.2.1⟩, hcond.2.2.2⟩
  apply hz
  have hmem := Finset.mem_image_of_mem (fun n : ℕ => (n : ℤ)) hnmem
  rw [Int.toNat_of_nonneg hcond.1] at hmem
  exact hmem

theorem opus_corr_gapPivotMass_eq_zero (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {q : ℕ} (x : (Fin q → ℕ) × (Fin m → ℤ))
    (hx : x ∉ gapPivotSupport S C N) : gapPivotMass S C N x.1 x.2 = 0 := by
  classical
  by_cases hp : x.1 ∈ independentPrimePoolSupport
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin q => (S.primeStage.pool N C.gap).upper)
  · have hz : x.2 ∉ pivotMassSupport S C N := fun hz =>
      hx (Finset.mem_product.mpr ⟨hp, hz⟩)
    have hnot : ¬ ∀ k, x.2 k ∈
        harmonicLawSupport (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) :=
      fun hall => hz (Fintype.mem_piFinset.mpr hall)
    push_neg at hnot
    obtain ⟨k, hk⟩ := hnot
    have hpiv : pivotMass S.core.parameters C N x.2 = 0 := by
      unfold pivotMass
      exact Finset.prod_eq_zero (Finset.mem_univ k) (opus_corr_harmonicLaw_eq_zero _ _ _ hk)
    simp [gapPivotMass, hpiv]
  · have hnot : ¬ ∀ i, x.1 i ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper :=
      fun hall => hp (Fintype.mem_piFinset.mpr hall)
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    have hslot : gapSlotMass S C.gap N x.1 = 0 := by
      unfold gapSlotMass independentPrimePoolMass
      exact Finset.prod_eq_zero (Finset.mem_univ i) (opus_corr_primePoolLaw_eq_zero _ _ _ hi)
    simp [gapPivotMass, hslot]

/-- A pool average of a function bounded by `δ` on the pool support is bounded by `δ`. -/
theorem opus_corr_poolAverage_abs_le (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K)
    (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper)
    (F : ℕ → ℝ) (δ : ℝ)
    (hF : ∀ k, k ∈ primePoolSupport (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper → |F k| ≤ δ) :
    |poolAverage S l N F| ≤ δ := by
  classical
  set lo := (S.primeStage.pool N l).lower
  set hi := (S.primeStage.pool N l).upper
  have hzero (k : ℕ) (hk : k ∉ primePoolSupport lo hi) : primePoolLaw lo hi k * F k = 0 := by
    rw [opus_corr_primePoolLaw_eq_zero lo hi k hk, zero_mul]
  have hzero' (k : ℕ) (hk : k ∉ primePoolSupport lo hi) : primePoolLaw lo hi k = 0 :=
    opus_corr_primePoolLaw_eq_zero lo hi k hk
  have hsum : ∑ k ∈ primePoolSupport lo hi, primePoolLaw lo hi k = 1 := by
    have h := primePoolLaw_tsum_one lo hi hMass
    rw [tsum_eq_sum (s := primePoolSupport lo hi) hzero'] at h
    exact h
  unfold poolAverage
  rw [tsum_eq_sum (s := primePoolSupport lo hi) hzero]
  calc
    |∑ k ∈ primePoolSupport lo hi, primePoolLaw lo hi k * F k| ≤
        ∑ k ∈ primePoolSupport lo hi, |primePoolLaw lo hi k * F k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ primePoolSupport lo hi, primePoolLaw lo hi k * δ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (primePoolLaw_nonneg lo hi k hMass)]
      exact mul_le_mul_of_nonneg_left (hF k hk) (primePoolLaw_nonneg lo hi k hMass)
    _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Exchange of the gap/pivot average and a pool average (both finitely supported). -/
theorem opus_corr_tsum_poolAverage_comm (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {q : ℕ}
    (H : (Fin q → ℕ) × (Fin m → ℤ) → ℕ → ℝ) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * poolAverage S C.gap N (H x) =
      poolAverage S C.gap N (fun k =>
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * H x k) := by
  classical
  set lo := (S.primeStage.pool N C.gap).lower
  set hi := (S.primeStage.pool N C.gap).upper
  have hP (G : ℕ → ℝ) : poolAverage S C.gap N G =
      ∑ k ∈ primePoolSupport lo hi, primePoolLaw lo hi k * G k := by
    unfold poolAverage
    apply tsum_eq_sum
    intro k hk
    rw [opus_corr_primePoolLaw_eq_zero lo hi k hk, zero_mul]
  have hX (G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) :
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x =
        ∑ x ∈ gapPivotSupport S C N, gapPivotMass S C N x.1 x.2 * G x := by
    apply tsum_eq_sum
    intro x hx
    rw [opus_corr_gapPivotMass_eq_zero S C N x hx, zero_mul]
  rw [hX, hP]
  simp_rw [hP, hX]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro x hx
  ring

end BalancedTools


section BalancedSlices

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

theorem opus_corr_join_update (u : Fin m) (y t : ℤ)
    (w : ∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) :
    Function.update (pkgMask_coordinateJoin u y w) u t = pkgMask_coordinateJoin u t w := by
  funext k
  by_cases hk : k = u
  · subst k
    simp [Function.update_self, pkgMask_coordinateJoin_at]
  · let i : finsetComplement ({u} : Finset (Fin m)) :=
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro hmem
        exact hk (Finset.mem_singleton.mp hmem)⟩⟩
    rw [Function.update_of_ne hk, pkgMask_coordinateJoin_other u y w i,
      pkgMask_coordinateJoin_other u t w i]

/-- Slicing the gap/pivot average along the pivot coordinate `u`. -/
theorem opus_corr_gapPivot_slice (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {q : ℕ} (u : Fin m)
    (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x =
      ∑' o : (Fin q → ℕ) × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
        (gapSlotMass S C.gap N o.1 * pkgMask_pivotRestMass S C N u o.2) *
          ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
            F (o.1, pkgMask_coordinateJoin u y o.2) := by
  rw [← pkgMask_gapPivotTsum_fubini S C N F]
  rw [← pkgMask_gapRestTsum_fubini S C N u (fun o =>
    ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
      F (o.1, pkgMask_coordinateJoin u y o.2))]
  apply tsum_congr
  intro p
  congr 1
  exact pkgMask_pivotTsum_coordinate_split S C N u (fun z => F (p, z))

/-- If every slice along `u` of two integrands differs by at most `δ`, so do their averages. -/
theorem opus_corr_gapPivot_slice_error (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    {q : ℕ} (u : Fin m) (F G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ o : (Fin q → ℕ) × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
      |(∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
          F (o.1, pkgMask_coordinateJoin u y o.2)) -
        ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
          G (o.1, pkgMask_coordinateJoin u y o.2)| ≤ δ) :
    |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) -
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x| ≤ δ := by
  rw [opus_corr_gapPivot_slice S C N u F, opus_corr_gapPivot_slice S C N u G]
  let FA : (Fin q → ℕ) × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) → ℝ := fun o =>
    ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
      F (o.1, pkgMask_coordinateJoin u y o.2)
  let FB : (Fin q → ℕ) × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ) → ℝ := fun o =>
    ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
      G (o.1, pkgMask_coordinateJoin u y o.2)
  have h1 := pkgMask_gapRestMass_mul_summable S C N u FA
  have h2 := pkgMask_gapRestMass_mul_summable S C N u FB
  change |(∑' o, (gapSlotMass S C.gap N o.1 * pkgMask_pivotRestMass S C N u o.2) * FA o) -
    ∑' o, (gapSlotMass S C.gap N o.1 * pkgMask_pivotRestMass S C N u o.2) * FB o| ≤ δ
  rw [← h1.tsum_sub h2]
  simp_rw [← mul_sub]
  exact pkgMask_gapRestAverage_error_le S C N u hMass (fun o => FA o - FB o) δ hδ h

/-- `|Σ μ E| ≤ δ` along a slice decomposition when each slice average is at most `δ`. -/
theorem opus_corr_gapPivot_slice_abs_le (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    {q : ℕ} (u : Fin m) (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ o : (Fin q → ℕ) × (∀ i : finsetComplement ({u} : Finset (Fin m)), ℤ),
      |∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
          F (o.1, pkgMask_coordinateJoin u y o.2)| ≤ δ) :
    |∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x| ≤ δ := by
  rw [opus_corr_gapPivot_slice S C N u F]
  exact pkgMask_gapRestAverage_error_le S C N u hMass _ δ hδ h

/-- A pool prime exceeds `V_l`, hence `w`, and is coprime to `W`. -/
theorem opus_corr_pool_prime_coprime (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K)
    (N k : ℕ) (hlow : FromArithmetic.masterScaleV S.core.parameters N l <
      (S.primeStage.pool N l).lower)
    (hk : k ∈ primePoolSupport (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper) :
    k.Prime ∧ FromArithmetic.masterScaleV S.core.parameters N l < k ∧
      k < (S.primeStage.pool N l).upper ∧ Nat.Coprime k (primorial (N + 1)) := by
  simp only [primePoolSupport, Finset.mem_filter, Finset.mem_Ico] at hk
  obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hk
  have hV : FromArithmetic.masterScaleV S.core.parameters N l < k := lt_of_lt_of_le hlow hlo
  refine ⟨hprime, hV, hhi, ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd hprime]
  intro hdvd
  have hle : k ≤ primorial (N + 1) := Nat.le_of_dvd (primorial_pos (N + 1)) hdvd
  have hW : primorial (N + 1) ≤ FromArithmetic.masterScaleV S.core.parameters N l := by
    have := S.core.parameters.Wle N
    unfold FromArithmetic.masterScaleV
    omega
  omega

end BalancedSlices


section BalancedEstimates

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- The multiplier `η_k(y)=k1_{k∣y}` of equation `eq:balanced-prime-substitution`. -/
def opus_corr_eta (k : ℕ) (y : ℤ) : ℝ := if (k : ℤ) ∣ y then (k : ℝ) else 0

/-- The balanced substitution `z_u ↦ z_u/k`, `z_v ↦ kz_v` (exact when `k ∣ z_u`). -/
def opus_corr_balancedVec {m : ℕ} (u v : Fin m) (k : ℕ) (z : Fin m → ℤ) : Fin m → ℤ :=
  Function.update (Function.update z v ((k : ℤ) * z v)) u (z u / (k : ℤ))

theorem opus_corr_rpow_natCast_bound {V : ℕ} {A : ℕ} {x : ℝ}
    (h : |x| ≤ (V : ℝ) ^ A) : |x| ≤ (V : ℝ) ^ (A : ℝ) := by
  rwa [Real.rpow_natCast]

/-- Prime insertion in coordinate `v` (Lemma `lem:prime-insertion`), averaged over the old
slots and the other pivots, uniformly over integrands bounded by `V^A`. -/
theorem opus_corr_insertion_estimate (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (v : Fin m) (A : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, ∀ (q : ℕ) (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ),
      (∀ x, |F x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A) →
      |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) -
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          poolAverage S C.gap N (fun k =>
            F (x.1, Function.update x.2 v ((k : ℤ) * x.2 v)))| ≤ δ := by
  intro δ hδ
  filter_upwards [prime_insertion_average_aux S C.gap (C.block v).1 (C.pivots_after_gap v)
      (A : ℝ) δ hδ, primePoolMass_pos_eventually S C.gap] with N hN hMass
  intro q F hF
  apply opus_corr_gapPivot_slice_error S C N hMass v _ _ δ hδ.le
  intro o
  have hswap :
      (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block v).1) (primorial (N + 1)) y *
        poolAverage S C.gap N (fun k =>
          F (o.1, Function.update (pkgMask_coordinateJoin v y o.2) v
            ((k : ℤ) * pkgMask_coordinateJoin v y o.2 v)))) =
      poolAverage S C.gap N (fun k =>
        ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block v).1) (primorial (N + 1)) y *
          F (o.1, pkgMask_coordinateJoin v ((k : ℤ) * y) o.2)) := by
    rw [pkgMask_poolAverage_tsum_pivot_interchange]
    apply tsum_congr
    intro y
    congr 1
    congr 1
    funext k
    rw [pkgMask_coordinateJoin_at, opus_corr_join_update]
  simp only
  rw [hswap]
  exact hN (fun y => F (o.1, pkgMask_coordinateJoin v y o.2))
    (fun y => opus_corr_rpow_natCast_bound (hF _))

/-- The fixed dilation of Lemma `lem:prime-insertion` in coordinate `u`, read at `z_u/k`,
uniformly over pool primes `k` and integrands bounded by `V^A`. -/
theorem opus_corr_dilation_estimate (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u : Fin m) (A : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, ∀ (q k : ℕ),
      k ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper →
      ∀ F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ,
      (∀ x, |F x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A) →
      |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) -
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          (opus_corr_eta k (x.2 u) * F (x.1, Function.update x.2 u (x.2 u / (k : ℤ))))| ≤ δ := by
  intro δ hδ
  filter_upwards [(prime_insertion_fixed_dilation_aux S C.gap (C.block u).1
      (C.pivots_after_gap u) 1).2 (A : ℝ) δ hδ, primePoolMass_pos_eventually S C.gap,
      pool_lower_gt_masterScaleV_eventually S C.gap] with N hN hMass hlow
  intro q k hk F hF
  obtain ⟨hprime, _, hhi, hcop⟩ := opus_corr_pool_prime_coprime S C.gap N k hlow hk
  have hkpos : 0 < k := hprime.pos
  have hkle : k ≤ ((S.primeStage.pool N C.gap).upper +
      FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ 1 := by
    rw [pow_one]; omega
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hkpos.ne'
  apply opus_corr_gapPivot_slice_error S C N hMass u _ _ δ hδ.le
  intro o
  have h := hN k hkpos hcop hkle (fun y => F (o.1, pkgMask_coordinateJoin u (y / (k : ℤ)) o.2))
    (fun y => opus_corr_rpow_natCast_bound (hF _))
  have hleft : (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y *
        F (o.1, pkgMask_coordinateJoin u ((k : ℤ) * y / (k : ℤ)) o.2)) =
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
        F (o.1, pkgMask_coordinateJoin u y o.2) := by
    apply tsum_congr
    intro y
    rw [Int.mul_ediv_cancel_left _ hk0]
  have hright : (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y *
        ((if (k : ℤ) ∣ y then (k : ℝ) else 0) *
          F (o.1, pkgMask_coordinateJoin u (y / (k : ℤ)) o.2))) =
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
        (opus_corr_eta k (pkgMask_coordinateJoin u y o.2 u) *
          F (o.1, Function.update (pkgMask_coordinateJoin u y o.2) u
            (pkgMask_coordinateJoin u y o.2 u / (k : ℤ)))) := by
    apply tsum_congr
    intro y
    rw [pkgMask_coordinateJoin_at, opus_corr_join_update]
    rfl
  rw [← hleft, ← hright]
  exact h

end BalancedEstimates


section BalancedEstimates2

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

theorem opus_corr_poolAverage_sub (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K)
    (N : ℕ) (F G : ℕ → ℝ) :
    poolAverage S l N F - poolAverage S l N G = poolAverage S l N (fun k => F k - G k) := by
  classical
  have hP (H : ℕ → ℝ) : poolAverage S l N H =
      ∑ k ∈ primePoolSupport (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper,
        primePoolLaw (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper k * H k := by
    unfold poolAverage
    apply tsum_eq_sum
    intro k hk
    rw [opus_corr_primePoolLaw_eq_zero _ _ k hk, zero_mul]
  rw [hP F, hP G, hP, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The balanced insertion (04:176–190): inserting `p` in coordinate `v` and then dilating
coordinate `u` by `p` changes the average by `o(1)`, uniformly over integrands bounded by
`V^A`. -/
theorem opus_corr_balanced_insertion_estimate (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u v : Fin m) (huv : u ≠ v) (A : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, ∀ (q : ℕ) (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ),
      (∀ x, |F x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A) →
      |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) -
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          poolAverage S C.gap N (fun k =>
            opus_corr_eta k (x.2 u) * F (x.1, opus_corr_balancedVec u v k x.2))| ≤ δ := by
  intro δ hδ
  filter_upwards [opus_corr_insertion_estimate S C v A (δ / 2) (by positivity),
    opus_corr_dilation_estimate S C u A (δ / 2) (by positivity),
    primePoolMass_pos_eventually S C.gap] with N hIns hDil hMass
  intro q F hF
  have h1 := hIns q F hF
  set I₁ := ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
    poolAverage S C.gap N (fun k => F (x.1, Function.update x.2 v ((k : ℤ) * x.2 v)))
  set I₂ := ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
    poolAverage S C.gap N (fun k =>
      opus_corr_eta k (x.2 u) * F (x.1, opus_corr_balancedVec u v k x.2))
  have h2 : |I₁ - I₂| ≤ δ / 2 := by
    simp only [I₁, I₂]
    rw [opus_corr_tsum_poolAverage_comm, opus_corr_tsum_poolAverage_comm,
      opus_corr_poolAverage_sub]
    apply opus_corr_poolAverage_abs_le S C.gap N hMass _ _
    intro k hk
    let Fk : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
      F (x.1, Function.update x.2 v ((k : ℤ) * x.2 v))
    have hFk : ∀ x, |Fk x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A :=
      fun x => hF _
    have h := hDil q k hk Fk hFk
    have hEq : ∀ x : (Fin q → ℕ) × (Fin m → ℤ),
        Fk (x.1, Function.update x.2 u (x.2 u / (k : ℤ))) =
          F (x.1, opus_corr_balancedVec u v k x.2) := by
      intro x
      simp only [Fk, opus_corr_balancedVec]
      rw [Function.update_of_ne (Ne.symm huv), Function.update_comm huv]
    simp only [hEq] at h
    exact h
  calc
    |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) - I₂| ≤
        |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x) - I₁| +
          |I₁ - I₂| := abs_sub_le _ _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add h1 h2
    _ = δ := by ring

end BalancedEstimates2


section BalancedAbsorption

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

theorem opus_corr_pivotLaw_facts (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (u : Fin m) :
    (∀ y, 0 ≤ harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y) ∧
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y = 1 := by
  have hcut := S.gapStage.valid_raw_cutoffs N (C.block u).1
  have hW := primorial_pos (N + 1)
  have hNorm := harmonicNormalizer_pos_of_cutoff _ _ hW hcut
  refine ⟨fun y => harmonicLaw_nonneg_of_normalizer_pos _ _ hNorm y, ?_⟩
  exact harmonicLaw_tsum_one_of_normalizer_pos _ _ (by omega) hNorm

theorem opus_corr_harmonic_tsum_eq_sum (X W : ℕ) (f : ℤ → ℝ) :
    ∑' y : ℤ, harmonicLaw X W y * f y = ∑ y ∈ harmonicLawSupport X W, harmonicLaw X W y * f y := by
  apply tsum_eq_sum
  intro y hy
  rw [opus_corr_harmonicLaw_eq_zero X W y hy, zero_mul]

/-- A nonnegative finitely supported law of total mass one: averages of `|f| ≤ g`. -/
theorem opus_corr_harmonic_abs_le (X W : ℕ) (hμ : ∀ y, 0 ≤ harmonicLaw X W y) (f g : ℤ → ℝ)
    (hfg : ∀ y, |f y| ≤ g y) :
    |∑' y : ℤ, harmonicLaw X W y * f y| ≤ ∑' y : ℤ, harmonicLaw X W y * g y := by
  rw [opus_corr_harmonic_tsum_eq_sum, opus_corr_harmonic_tsum_eq_sum]
  calc
    |∑ y ∈ harmonicLawSupport X W, harmonicLaw X W y * f y| ≤
        ∑ y ∈ harmonicLawSupport X W, |harmonicLaw X W y * f y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ harmonicLawSupport X W, harmonicLaw X W y * g y := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (hμ y)]
      exact mul_le_mul_of_nonneg_left (hfg y) (hμ y)

theorem opus_corr_eta_mul_self (k : ℕ) (y : ℤ) :
    opus_corr_eta k y * opus_corr_eta k y = (k : ℝ) * opus_corr_eta k y := by
  unfold opus_corr_eta
  split_ifs <;> simp

theorem opus_corr_eta_nonneg (k : ℕ) (y : ℤ) : 0 ≤ opus_corr_eta k y := by
  unfold opus_corr_eta
  split_ifs <;> positivity

/-- For distinct primes, `η_{k₁}η_{k₀}=η_{k₁k₀}`. -/
theorem opus_corr_eta_mul_of_ne {k₁ k₀ : ℕ} (h₁ : k₁.Prime) (h₀ : k₀.Prime) (hne : k₁ ≠ k₀)
    (y : ℤ) : opus_corr_eta k₁ y * opus_corr_eta k₀ y = opus_corr_eta (k₁ * k₀) y := by
  have hcop : IsCoprime (k₁ : ℤ) (k₀ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast (Nat.coprime_primes h₁ h₀).mpr hne
  unfold opus_corr_eta
  push_cast
  by_cases hd₁ : (k₁ : ℤ) ∣ y <;> by_cases hd₀ : (k₀ : ℤ) ∣ y
  · have hd : (k₁ : ℤ) * k₀ ∣ y := hcop.mul_dvd hd₁ hd₀
    rw [if_pos hd₁, if_pos hd₀, if_pos hd]
  · have hd : ¬ (k₁ : ℤ) * k₀ ∣ y := fun h => hd₀ (dvd_trans (dvd_mul_left _ _) h)
    rw [if_pos hd₁, if_neg hd₀, if_neg hd, mul_zero]
  · have hd : ¬ (k₁ : ℤ) * k₀ ∣ y := fun h => hd₁ (dvd_trans (dvd_mul_right _ _) h)
    rw [if_neg hd₁, if_pos hd₀, if_neg hd, zero_mul]
  · have hd : ¬ (k₁ : ℤ) * k₀ ∣ y := fun h => hd₁ (dvd_trans (dvd_mul_right _ _) h)
    rw [if_neg hd₁, if_neg hd₀, if_neg hd, zero_mul]

/-- `|E F| ≤ B` for `|F| ≤ B` under the gap/pivot law. -/
theorem opus_corr_gapPivot_abs_le (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    {q : ℕ} (F : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) (B : ℝ) (hF : ∀ x, |F x| ≤ B) :
    |∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * F x| ≤ B := by
  classical
  have hX (G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) :
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x =
        ∑ x ∈ gapPivotSupport S C N, gapPivotMass S C N x.1 x.2 * G x := by
    apply tsum_eq_sum
    intro x hx
    rw [opus_corr_gapPivotMass_eq_zero S C N x hx, zero_mul]
  have hone := gapPivotMass_tsum_one (q := q) S C N hMass
  have hone' : ∑ x ∈ gapPivotSupport (q := q) S C N, gapPivotMass S C N x.1 x.2 = 1 := by
    have := hX (fun _ => 1)
    simp only [mul_one] at this
    rw [← this, hone]
  rw [hX]
  calc
    |∑ x ∈ gapPivotSupport S C N, gapPivotMass S C N x.1 x.2 * F x| ≤
        ∑ x ∈ gapPivotSupport S C N, |gapPivotMass S C N x.1 x.2 * F x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ gapPivotSupport S C N, gapPivotMass S C N x.1 x.2 * B := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (gapPivotMass_nonneg S C N hMass x.1 x.2)]
      exact mul_le_mul_of_nonneg_left (hF x) (gapPivotMass_nonneg S C N hMass x.1 x.2)
    _ = B := by rw [← Finset.sum_mul, hone', one_mul]

end BalancedAbsorption


section BalancedAbsorption2

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- `E_y μ_u(y)η_k(y) ≤ 2` for pool primes `k`, eventually (Lemma `lem:prime-insertion` with
`F=1`). -/
theorem opus_corr_eta_average_le_two (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u : Fin m) :
    ∀ᶠ N in atTop, ∀ k ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper,
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
        opus_corr_eta k y ≤ 2 := by
  filter_upwards [(prime_insertion_fixed_dilation_aux S C.gap (C.block u).1
      (C.pivots_after_gap u) 1).2 0 (1 / 2) (by norm_num),
    pool_lower_gt_masterScaleV_eventually S C.gap] with N hN hlow
  intro k hk
  obtain ⟨hprime, _, hhi, hcop⟩ := opus_corr_pool_prime_coprime S C.gap N k hlow hk
  have hkle : k ≤ ((S.primeStage.pool N C.gap).upper +
      FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ 1 := by
    rw [pow_one]; omega
  have h := hN k hprime.pos hcop hkle (fun _ => 1) (fun _ => by simp)
  obtain ⟨_, hone⟩ := opus_corr_pivotLaw_facts S C N u
  simp only [mul_one] at h
  rw [hone] at h
  have heq : (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
      opus_corr_eta k y) = ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y * (if (k : ℤ) ∣ y then (k : ℝ) else 0) := rfl
  rw [heq]
  have := (abs_le.mp h).1
  linarith

/-- The diagonal `p=q` before absorption has weighted mass `≤ 2kB` (04:228–236). -/
theorem opus_corr_eta_sq_average_le (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u : Fin m) :
    ∀ᶠ N in atTop, ∀ k ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper,
      ∀ (q : ℕ) (G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) (B : ℝ), 0 ≤ B → (∀ x, |G x| ≤ B) →
      |∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          (opus_corr_eta k (x.2 u) * opus_corr_eta k (x.2 u) * G x)| ≤ 2 * k * B := by
  filter_upwards [opus_corr_eta_average_le_two S C u, primePoolMass_pos_eventually S C.gap]
    with N hN hMass
  intro k hk q G B hB hG
  obtain ⟨hμ, _⟩ := opus_corr_pivotLaw_facts S C N u
  apply opus_corr_gapPivot_slice_abs_le S C N hMass u _ _ (by positivity)
  intro o
  set X := S.core.parameters.X N (C.block u).1
  set W := primorial (N + 1)
  calc
    |∑' y : ℤ, harmonicLaw X W y *
        (opus_corr_eta k (pkgMask_coordinateJoin u y o.2 u) *
          opus_corr_eta k (pkgMask_coordinateJoin u y o.2 u) *
            G (o.1, pkgMask_coordinateJoin u y o.2))| ≤
        ∑' y : ℤ, harmonicLaw X W y * ((k : ℝ) * B * opus_corr_eta k y) := by
      apply opus_corr_harmonic_abs_le X W hμ
      intro y
      rw [pkgMask_coordinateJoin_at, opus_corr_eta_mul_self, abs_mul,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (opus_corr_eta_nonneg k y))]
      calc
        (k : ℝ) * opus_corr_eta k y * |G (o.1, pkgMask_coordinateJoin u y o.2)| ≤
            (k : ℝ) * opus_corr_eta k y * B :=
          mul_le_mul_of_nonneg_left (hG _)
            (mul_nonneg (Nat.cast_nonneg k) (opus_corr_eta_nonneg k y))
        _ = (k : ℝ) * B * opus_corr_eta k y := by ring
    _ = (k : ℝ) * B * ∑' y : ℤ, harmonicLaw X W y * opus_corr_eta k y := by
      rw [opus_corr_harmonic_tsum_eq_sum, opus_corr_harmonic_tsum_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (k : ℝ) * B * 2 :=
      mul_le_mul_of_nonneg_left (hN k hk) (mul_nonneg (Nat.cast_nonneg k) hB)
    _ = 2 * k * B := by ring

/-- The off-diagonal absorption `η_pη_q = pq1_{pq∣z_u} ↦ z_u ↦ pqz_u` (04:236–240). -/
theorem opus_corr_offdiag_absorption (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u : Fin m) (A : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, ∀ k₁ ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper,
      ∀ k₀ ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper, k₁ ≠ k₀ →
      ∀ (q : ℕ) (G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ),
      (∀ x, |G x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A) →
      |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          (opus_corr_eta k₁ (x.2 u) * opus_corr_eta k₀ (x.2 u) * G x)) -
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          G (x.1, Function.update x.2 u ((k₁ : ℤ) * k₀ * x.2 u))| ≤ δ := by
  intro δ hδ
  filter_upwards [(prime_insertion_fixed_dilation_aux S C.gap (C.block u).1
      (C.pivots_after_gap u) 2).2 (A : ℝ) δ hδ, primePoolMass_pos_eventually S C.gap,
    pool_lower_gt_masterScaleV_eventually S C.gap] with N hN hMass hlow
  intro k₁ hk₁ k₀ hk₀ hne q G hG
  obtain ⟨hp₁, _, hhi₁, hcop₁⟩ := opus_corr_pool_prime_coprime S C.gap N k₁ hlow hk₁
  obtain ⟨hp₀, _, hhi₀, hcop₀⟩ := opus_corr_pool_prime_coprime S C.gap N k₀ hlow hk₀
  set hi := (S.primeStage.pool N C.gap).upper
  set V := FromArithmetic.masterScaleV S.core.parameters N C.gap
  have hkpos : 0 < k₁ * k₀ := Nat.mul_pos hp₁.pos hp₀.pos
  have hkcop : Nat.Coprime (k₁ * k₀) (primorial (N + 1)) := Nat.coprime_mul_iff_left.mpr ⟨hcop₁, hcop₀⟩
  have hkle : k₁ * k₀ ≤ (hi + V) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  rw [abs_sub_comm]
  apply opus_corr_gapPivot_slice_error S C N hMass u _ _ δ hδ.le
  intro o
  have h := hN (k₁ * k₀) hkpos hkcop hkle (fun y => G (o.1, pkgMask_coordinateJoin u y o.2))
    (fun y => opus_corr_rpow_natCast_bound (hG _))
  have hleft : (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y *
        G (o.1, Function.update (pkgMask_coordinateJoin u y o.2) u
          ((k₁ : ℤ) * k₀ * pkgMask_coordinateJoin u y o.2 u))) =
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
        G (o.1, pkgMask_coordinateJoin u (((k₁ * k₀ : ℕ) : ℤ) * y) o.2) := by
    apply tsum_congr
    intro y
    rw [pkgMask_coordinateJoin_at, opus_corr_join_update]
    push_cast
    rfl
  have hright : (∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1)
        (primorial (N + 1)) y *
        (opus_corr_eta k₁ (pkgMask_coordinateJoin u y o.2 u) *
          opus_corr_eta k₀ (pkgMask_coordinateJoin u y o.2 u) *
            G (o.1, pkgMask_coordinateJoin u y o.2))) =
      ∑' y : ℤ, harmonicLaw (S.core.parameters.X N (C.block u).1) (primorial (N + 1)) y *
        ((if (((k₁ * k₀ : ℕ)) : ℤ) ∣ y then ((k₁ * k₀ : ℕ) : ℝ) else 0) *
          G (o.1, pkgMask_coordinateJoin u y o.2)) := by
    apply tsum_congr
    intro y
    rw [pkgMask_coordinateJoin_at, opus_corr_eta_mul_of_ne hp₁ hp₀ hne]
    rfl
  simp only
  rw [hleft, hright]
  exact h

end BalancedAbsorption2


section BalancedAbsorption3

variable {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

theorem opus_corr_pairLaw_tsum_eq_sum (lo hi : ℕ) (H : ℕ × ℕ → ℝ) :
    ∑' kk : ℕ × ℕ, (primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) * H kk =
      ∑ kk ∈ primePoolSupport lo hi ×ˢ primePoolSupport lo hi,
        (primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) * H kk := by
  apply tsum_eq_sum
  intro kk hkk
  rcases Finset.mem_product.not.mp hkk |> not_and_or.mp with h | h
  · rw [opus_corr_primePoolLaw_eq_zero lo hi _ h]; ring
  · rw [opus_corr_primePoolLaw_eq_zero lo hi _ h]; ring

/-- Exchange of the gap/pivot average and the average over a fresh prime pair. -/
theorem opus_corr_tsum_pair_comm (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) {q : ℕ}
    (H : (Fin q → ℕ) × (Fin m → ℤ) → ℕ × ℕ → ℝ) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∑' kk : ℕ × ℕ, (primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper kk.1 *
          primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.2) * H x kk =
      ∑ kk ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper ×ˢ
          primePoolSupport (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper,
        (primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper kk.1 *
          primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.2) *
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * H x kk := by
  classical
  have hX (G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ) :
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x =
        ∑ x ∈ gapPivotSupport S C N, gapPivotMass S C N x.1 x.2 * G x := by
    apply tsum_eq_sum
    intro x hx
    rw [opus_corr_gapPivotMass_eq_zero S C N x hx, zero_mul]
  simp_rw [opus_corr_pairLaw_tsum_eq_sum, hX, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro kk _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The second Cauchy–Schwarz factor of the balanced step after discarding `p=q`, absorbing
`pq1_{pq∣z_u}` and reinstating `p=q` (04:228–247), uniformly over integrands bounded by
`V^A`. -/
theorem opus_corr_absorption_estimate (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (u : Fin m) (A : ℕ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      ∀ (q : ℕ) (G : ℕ → ℕ → (Fin q → ℕ) × (Fin m → ℤ) → ℝ),
      (∀ k₁ k₀ x, |G k₁ k₀ x| ≤ (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ A) →
      |(∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          ∑' kk : ℕ × ℕ, (primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.1 *
            primePoolLaw (S.primeStage.pool N C.gap).lower
              (S.primeStage.pool N C.gap).upper kk.2) *
            (opus_corr_eta kk.1 (x.2 u) * opus_corr_eta kk.2 (x.2 u) * G kk.1 kk.2 x)) -
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          ∑' kk : ℕ × ℕ, (primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.1 *
            primePoolLaw (S.primeStage.pool N C.gap).lower
              (S.primeStage.pool N C.gap).upper kk.2) *
            G kk.1 kk.2 (x.1, Function.update x.2 u ((kk.1 : ℤ) * kk.2 * x.2 u))| ≤ δ := by
  intro δ hδ
  have hsmall := primePoolMass_inverse_superpolynomial S C.gap ((A : ℝ) + 1) (by positivity)
  have hsmall' : ∀ᶠ N in atTop,
      (primePoolMass (S.primeStage.pool N C.gap).lower (S.primeStage.pool N C.gap).upper)⁻¹ *
        (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) ^ ((A : ℝ) + 1) < δ / 8 :=
    hsmall.eventually_lt_const (by positivity)
  filter_upwards [opus_corr_offdiag_absorption S C u A (δ / 2) (by positivity),
    opus_corr_eta_sq_average_le S C u, primePoolMass_pos_eventually S C.gap, hsmall']
    with N hOff hDiag hMass hS
  intro q G hG
  set lo := (S.primeStage.pool N C.gap).lower
  set hi := (S.primeStage.pool N C.gap).upper
  set V : ℝ := (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) with hVdef
  set P := primePoolSupport lo hi
  set Smass := primePoolMass lo hi
  have hV1 : 1 ≤ V := by
    have h2 : 1 ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
      unfold FromArithmetic.masterScaleV; omega
    rw [hVdef]
    exact_mod_cast h2
  have hVA : 0 ≤ V ^ A := by positivity
  let T₁ : ℕ × ℕ → ℝ := fun kk =>
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
      (opus_corr_eta kk.1 (x.2 u) * opus_corr_eta kk.2 (x.2 u) * G kk.1 kk.2 x)
  let T₂ : ℕ × ℕ → ℝ := fun kk =>
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
      G kk.1 kk.2 (x.1, Function.update x.2 u ((kk.1 : ℤ) * kk.2 * x.2 u))
  have hpair (kk : ℕ × ℕ) (hkk : kk ∈ P ×ˢ P) :
      |T₁ kk - T₂ kk| ≤ δ / 2 + (if kk.1 = kk.2 then 3 * (kk.1 : ℝ) * V ^ A else 0) := by
    obtain ⟨k₁, k₀⟩ := kk
    obtain ⟨hk₁, hk₀⟩ := Finset.mem_product.mp hkk
    simp only at hk₁ hk₀ ⊢
    by_cases heq : k₁ = k₀
    · subst heq
      rw [if_pos rfl]
      have h1 : |T₁ (k₁, k₁)| ≤ 2 * k₁ * V ^ A :=
        hDiag k₁ hk₁ q (G k₁ k₁) (V ^ A) hVA (fun x => hG _ _ x)
      have h2 : |T₂ (k₁, k₁)| ≤ V ^ A :=
        opus_corr_gapPivot_abs_le S C N hMass _ _ (fun x => hG _ _ _)
      have hk1 : (1 : ℝ) ≤ k₁ := by
        have := (Finset.mem_filter.mp hk₁).2.one_lt
        exact_mod_cast this.le
      calc
        |T₁ (k₁, k₁) - T₂ (k₁, k₁)| ≤ |T₁ (k₁, k₁)| + |T₂ (k₁, k₁)| := abs_sub _ _
        _ ≤ 2 * k₁ * V ^ A + V ^ A := add_le_add h1 h2
        _ ≤ δ / 2 + 3 * (k₁ : ℝ) * V ^ A := by nlinarith
    · rw [if_neg heq, add_zero]
      exact hOff k₁ hk₁ k₀ hk₀ heq q (G k₁ k₀) (fun x => hG _ _ x)
  have hlam (k : ℕ) : 0 ≤ primePoolLaw lo hi k := primePoolLaw_nonneg lo hi k hMass
  have hlamSum : ∑ k ∈ P, primePoolLaw lo hi k = 1 := by
    have h := primePoolLaw_tsum_one lo hi hMass
    rw [tsum_eq_sum (s := P) (fun k hk => opus_corr_primePoolLaw_eq_zero lo hi k hk)] at h
    exact h
  have hlamSq : ∑ k ∈ P, (k : ℝ) * primePoolLaw lo hi k ^ 2 = Smass⁻¹ := by
    have h := primePoolLaw_secondMoment lo hi hMass
    rw [tsum_eq_sum (s := P) (fun k hk => by
      rw [opus_corr_primePoolLaw_eq_zero lo hi k hk]; ring)] at h
    exact h
  rw [opus_corr_tsum_pair_comm, opus_corr_tsum_pair_comm, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ kk ∈ P ×ˢ P, (primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) * (T₁ kk - T₂ kk)| ≤
        ∑ kk ∈ P ×ˢ P, |(primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) * (T₁ kk - T₂ kk)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ kk ∈ P ×ˢ P, (primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) *
          (δ / 2 + (if kk.1 = kk.2 then 3 * (kk.1 : ℝ) * V ^ A else 0)) := by
      apply Finset.sum_le_sum
      intro kk hkk
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hlam _) (hlam _))]
      exact mul_le_mul_of_nonneg_left (hpair kk hkk) (mul_nonneg (hlam _) (hlam _))
    _ = ∑ k₁ ∈ P, ∑ k₀ ∈ P, (primePoolLaw lo hi k₁ * primePoolLaw lo hi k₀) *
          (δ / 2 + (if k₁ = k₀ then 3 * (k₁ : ℝ) * V ^ A else 0)) := Finset.sum_product _ _ _
    _ = ∑ k₁ ∈ P, (primePoolLaw lo hi k₁ * (δ / 2) +
          3 * V ^ A * ((k₁ : ℝ) * primePoolLaw lo hi k₁ ^ 2)) := by
      apply Finset.sum_congr rfl
      intro k₁ hk₁
      have hsplit : ∀ k₀ ∈ P, (primePoolLaw lo hi k₁ * primePoolLaw lo hi k₀) *
          (δ / 2 + (if k₁ = k₀ then 3 * (k₁ : ℝ) * V ^ A else 0)) =
          primePoolLaw lo hi k₁ * (δ / 2) * primePoolLaw lo hi k₀ +
            (if k₁ = k₀ then primePoolLaw lo hi k₁ * primePoolLaw lo hi k₀ *
              (3 * (k₁ : ℝ) * V ^ A) else 0) := by
        intro k₀ _
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hlamSum,
        Finset.sum_ite_eq P k₁ (fun k₀ => primePoolLaw lo hi k₁ * primePoolLaw lo hi k₀ *
          (3 * (k₁ : ℝ) * V ^ A)), if_pos hk₁]
      ring
    _ = δ / 2 * (∑ k ∈ P, primePoolLaw lo hi k) ^ 2 +
          3 * V ^ A * ∑ k ∈ P, (k : ℝ) * primePoolLaw lo hi k ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hlamSum]
      ring
    _ = δ / 2 + 3 * (Smass⁻¹ * V ^ A) := by rw [hlamSum, hlamSq]; ring
    _ ≤ δ := by
      have hpow : V ^ A ≤ V ^ ((A : ℝ) + 1) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hV1 (by linarith)
      have hSinv : 0 ≤ Smass⁻¹ := inv_nonneg.mpr (primePoolMass_nonneg lo hi)
      have := mul_le_mul_of_nonneg_left hpow hSinv
      linarith

end BalancedAbsorption3


/-! ## The balanced step on mask-removal states -/

section BalancedState

variable {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- A row is invariant at the balanced step when its two branches are parallel. -/
def opus_corr_balancedInv (st : MaskRemovalState m q r) (u v : Fin m) (i : Fin r) : Prop :=
  ((st.shape.row i).scaleBalancedP u v).Parallel ((st.shape.row i).scaleBalancedQ u v)

/-- The weight `Ω` of the invariant rows. -/
noncomputable def opus_corr_balancedOmega (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (u v : Fin m) (x : (Fin q → ℕ) × (Fin m → ℤ)) : ℝ :=
  pkgMask_invariantRowWeight st S C a N (opus_corr_balancedInv st u v) x.1 x.2

/-- The integrand without the removed mask `U` (a valid state with one mask fewer). -/
def opus_corr_eraseMask (st : MaskRemovalState m q r) (U : Finset (Fin m)) :
    MaskRemovalState m q r :=
  ⟨st.shape, st.masks.erase U, st.maskFunction, st.rowFunction⟩

/-- The residual `H_p` of the balanced step (04:205–212) without its multiplier `η_p`. -/
noncomputable def opus_corr_balancedResidual (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (U : Finset (Fin m)) (u v : Fin m) (x : (Fin q → ℕ) × (Fin m → ℤ)) (k : ℕ) : ℝ :=
  MaskRemovalState.pkgMask_stateIntegrand (opus_corr_eraseMask st U) S C a N x.1
      (opus_corr_balancedVec u v k x.2) /
    opus_corr_balancedOmega st S C a N u v x

theorem opus_corr_balancedOmega_ge_one (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (u v : Fin m) (x : (Fin q → ℕ) × (Fin m → ℤ)) :
    1 ≤ opus_corr_balancedOmega st S C a N u v x := by
  classical
  unfold opus_corr_balancedOmega pkgMask_invariantRowWeight
  calc
    (1 : ℝ) = ∏ _i : Fin r, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
      intro i _
      by_cases hI : opus_corr_balancedInv st u v i
      · rw [dif_pos hI]
        have := chainWeight_nonneg S C N (st.shape.row i).anchor
          (rowForm (chainScale S.core.parameters C a N) (st.shape.row i) x.1
            (fun k => (x.2 k : ℚ))).num
        linarith
      · rw [dif_neg hI]

theorem opus_corr_eraseMask_valid (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ) (U : Finset (Fin m))
    (hvalid : st.Valid S C a N Jstar gstar) :
    (opus_corr_eraseMask st U).Valid S C a N Jstar gstar := by
  obtain ⟨h1, h2, h3, h4⟩ := hvalid
  exact ⟨h1, fun V hV => h2 V (Finset.mem_of_mem_erase hV), h3, h4⟩

/-- `η_kΦ(D_kz) = (b_U(z_U)Ω(z))·(η_kH_k(z))`: the removed mask is unchanged by the balanced
substitution on the support of `η_k` (04:186–205). -/
theorem opus_corr_balanced_factor (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (U : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v) (hU : U ∈ st.masks)
    (hu : u ∈ U) (hv : v ∈ U) (x : (Fin q → ℕ) × (Fin m → ℤ)) (k : ℕ) :
    opus_corr_eta k (x.2 u) *
        MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1 (opus_corr_balancedVec u v k x.2) =
      (st.maskFunction U x.1 (∏ j ∈ U, x.2 j) * opus_corr_balancedOmega st S C a N u v x) *
        (opus_corr_eta k (x.2 u) * opus_corr_balancedResidual st S C a N U u v x k) := by
  classical
  by_cases hd : (k : ℤ) ∣ x.2 u
  · have hprod : ∏ j ∈ U, opus_corr_balancedVec u v k x.2 j = ∏ j ∈ U, x.2 j := by
      unfold opus_corr_balancedVec
      rw [Function.update_comm (Ne.symm huv)]
      exact mask_product_balanced_update U u v hu hv huv x.2 k hd
    have hΩ : opus_corr_balancedOmega st S C a N u v x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le one_pos (opus_corr_balancedOmega_ge_one st S C a N u v x))
    unfold opus_corr_balancedResidual
    unfold MaskRemovalState.pkgMask_stateIntegrand
    simp only [opus_corr_eraseMask]
    rw [← Finset.mul_prod_erase st.masks _ hU, hprod]
    field_simp
  · simp [opus_corr_eta, hd]

/-- `|E(b_UΩ)·E_pη_pH_p|² ≤ (EΩ)·E[Ω(E_pη_pH_p)²]` (equation `eq:mask-weighted-cs`). -/
theorem opus_corr_balanced_cs (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (Jstar : Finset (Fin m)) (gstar : ℤ → ℝ)
    (hvalid : st.Valid S C a N Jstar gstar)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    (U : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v) (hU : U ∈ st.masks)
    (hu : u ∈ U) (hv : v ∈ U) :
    |∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
          MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1
            (opus_corr_balancedVec u v k x.2))| ^ 2 ≤
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          opus_corr_balancedOmega st S C a N u v x) *
        ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          (opus_corr_balancedOmega st S C a N u v x *
            (poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
              opus_corr_balancedResidual st S C a N U u v x k)) ^ 2) := by
  let Ω := opus_corr_balancedOmega st S C a N u v
  let H₀ : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
    st.maskFunction U x.1 (∏ j ∈ U, x.2 j) * Ω x
  let H₁ : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
    poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
      opus_corr_balancedResidual st S C a N U u v x k)
  have hΩ : ∀ x, 0 ≤ Ω x := fun x =>
    le_trans zero_le_one (opus_corr_balancedOmega_ge_one st S C a N u v x)
  have h0 : ∀ x, |H₀ x| ≤ Ω x := by
    intro x
    simp only [H₀]
    rw [abs_mul, abs_of_nonneg (hΩ x)]
    have hb := hvalid.2.1 U hU x.1 (∏ j ∈ U, x.2 j)
    calc
      |st.maskFunction U x.1 (∏ j ∈ U, x.2 j)| * Ω x ≤ 1 * Ω x :=
        mul_le_mul_of_nonneg_right hb (hΩ x)
      _ = Ω x := one_mul _
  have hrewrite : ∀ x : (Fin q → ℕ) × (Fin m → ℤ),
      poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
          MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1
            (opus_corr_balancedVec u v k x.2)) = H₀ x * H₁ x := by
    intro x
    simp only [H₀, H₁]
    rw [← pkgMask_poolAverage_const_mul]
    congr 1
    funext k
    exact opus_corr_balanced_factor st S C a N U u v huv hU hu hv x k
  simp_rw [hrewrite]
  exact gapPivot_weighted_cauchy_schwarz S C N hMass Ω H₀ H₁ hΩ h0

/-- The square of the residual average, expanded over two independent fresh primes. -/
theorem opus_corr_balanced_square_expand (st : MaskRemovalState m q r)
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (U : Finset (Fin m)) (u v : Fin m) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        (opus_corr_balancedOmega st S C a N u v x *
          (poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
            opus_corr_balancedResidual st S C a N U u v x k)) ^ 2) =
      ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∑' kk : ℕ × ℕ, (primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper kk.1 *
          primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.2) *
          (opus_corr_eta kk.1 (x.2 u) * opus_corr_eta kk.2 (x.2 u) *
            (opus_corr_balancedOmega st S C a N u v x *
              opus_corr_balancedResidual st S C a N U u v x kk.1 *
              opus_corr_balancedResidual st S C a N U u v x kk.2)) := by
  apply tsum_congr
  intro x
  congr 1
  rw [sq, pkgMask_poolAverage_mul, ← tsum_mul_left]
  apply tsum_congr
  intro kk
  ring

end BalancedState


/-! ## The two balanced branches and the next state -/

section BalancedBranches

variable {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- The `P` branch `(z_u,z_v) ↦ (p₀z_u,p₁z_v)` of equation `eq:prime-two-branches`. -/
def opus_corr_branchP {m : ℕ} (u v : Fin m) (p₀ p₁ : ℕ) (z : Fin m → ℤ) : Fin m → ℤ :=
  Function.update (Function.update z u ((p₀ : ℤ) * z u)) v ((p₁ : ℤ) * z v)

/-- The `Q` branch `(z_u,z_v) ↦ (p₁z_u,p₀z_v)`. -/
def opus_corr_branchQ {m : ℕ} (u v : Fin m) (p₀ p₁ : ℕ) (z : Fin m → ℤ) : Fin m → ℤ :=
  Function.update (Function.update z v ((p₀ : ℤ) * z v)) u ((p₁ : ℤ) * z u)

theorem opus_corr_branchP_cast {m : ℕ} (u v : Fin m) (huv : u ≠ v) (p₀ p₁ : ℕ)
    (z : Fin m → ℤ) :
    (fun k => (opus_corr_branchP u v p₀ p₁ z k : ℚ)) =
      Function.update (Function.update (fun k => (z k : ℚ)) u ((p₀ : ℚ) * (z u : ℚ))) v
        ((p₁ : ℚ) * (z v : ℚ)) := by
  funext k
  unfold opus_corr_branchP
  by_cases hkv : k = v
  · subst k; simp [Function.update_self]
  · by_cases hku : k = u
    · subst k; simp [Function.update_self, Function.update_of_ne hkv]
    · simp [Function.update_of_ne hkv, Function.update_of_ne hku]

theorem opus_corr_branchQ_cast {m : ℕ} (u v : Fin m) (huv : u ≠ v) (p₀ p₁ : ℕ)
    (z : Fin m → ℤ) :
    (fun k => (opus_corr_branchQ u v p₀ p₁ z k : ℚ)) =
      Function.update (Function.update (fun k => (z k : ℚ)) v ((p₀ : ℚ) * (z v : ℚ))) u
        ((p₁ : ℚ) * (z u : ℚ)) := by
  funext k
  unfold opus_corr_branchQ
  by_cases hku : k = u
  · subst k; simp [Function.update_self]
  · by_cases hkv : k = v
    · subst k; simp [Function.update_self, Function.update_of_ne hku]
    · simp [Function.update_of_ne hkv, Function.update_of_ne hku]

/-- After absorption `z_u ↦ p₁p₀z_u`, the balanced substitution with `p₁` is the `P` branch. -/
theorem opus_corr_balancedVec_absorb_P {m : ℕ} (u v : Fin m) (huv : u ≠ v) (p₁ p₀ : ℕ)
    (hp₁ : p₁ ≠ 0) (z : Fin m → ℤ) :
    opus_corr_balancedVec u v p₁ (Function.update z u ((p₁ : ℤ) * p₀ * z u)) =
      opus_corr_branchP u v p₀ p₁ z := by
  have hp₁' : (p₁ : ℤ) ≠ 0 := by exact_mod_cast hp₁
  funext k
  unfold opus_corr_balancedVec opus_corr_branchP
  by_cases hku : k = u
  · subst k
    simp only [Function.update_self]
    rw [mul_assoc, Int.mul_ediv_cancel_left _ hp₁', Function.update_of_ne huv,
      Function.update_self]
  · by_cases hkv : k = v
    · subst k
      simp [Function.update_of_ne hku, Function.update_self]
    · simp [Function.update_of_ne hku, Function.update_of_ne hkv]

/-- After absorption, the balanced substitution with `p₀` is the `Q` branch. -/
theorem opus_corr_balancedVec_absorb_Q {m : ℕ} (u v : Fin m) (huv : u ≠ v) (p₁ p₀ : ℕ)
    (hp₀ : p₀ ≠ 0) (z : Fin m → ℤ) :
    opus_corr_balancedVec u v p₀ (Function.update z u ((p₁ : ℤ) * p₀ * z u)) =
      opus_corr_branchQ u v p₀ p₁ z := by
  have hp₀' : (p₀ : ℤ) ≠ 0 := by exact_mod_cast hp₀
  funext k
  unfold opus_corr_balancedVec opus_corr_branchQ
  by_cases hku : k = u
  · subst k
    simp only [Function.update_self]
    rw [show (p₁ : ℤ) * p₀ * z u = (p₀ : ℤ) * (p₁ * z u) by ring,
      Int.mul_ediv_cancel_left _ hp₀']
  · by_cases hkv : k = v
    · subst k
      simp [Function.update_of_ne hku, Function.update_self]
    · simp [Function.update_of_ne hku, Function.update_of_ne hkv]

/-- The balanced analogue of `pkgMask_outsideBranchStateIntegrand_identity`: the invariant
weights at the `P` branch times the next-state integrand are the product of the two branch
integrands (04:241–262). -/
theorem opus_corr_balancedBranchStateIntegrand_identity {r' : ℕ}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBalancedP u v)
      (fun i => (st.shape.row i).scaleBalancedQ u v) x.val.1 x.val.2)
    (p : Fin (q + 2) → ℕ)
    (hgood : p ∈ independentPrimePoolSupport
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper))
    (z : Fin m → ℤ) (hp : ∀ j, p j ≠ 0)
    (hdenNew : ∀ T : RowTemplate m (q + 2),
      (rowForm (chainScale S.core.parameters C a N) T p fun k => (z k : ℚ)).den = 1) :
    (∏ i : Fin r, if hi :
        ((st.shape.row i).scaleBalancedP u v).Parallel ((st.shape.row i).scaleBalancedQ u v) then
          1 + chainWeight S.core.parameters C N (st.shape.row i).anchor
            (rowForm (chainScale S.core.parameters C a N)
              ((st.shape.row i).scaleBalancedP u v) p (fun k => (z k : ℚ))).num
        else 1) *
      MaskRemovalState.pkgMask_stateIntegrand
        (pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e) S C a N p z =
      MaskRemovalState.pkgMask_stateIntegrand (opus_corr_eraseMask st U) S C a N
          (dropPrimeTuple2 p) (opus_corr_branchP u v (p 0) (p 1) z) *
        MaskRemovalState.pkgMask_stateIntegrand (opus_corr_eraseMask st U) S C a N
          (dropPrimeTuple2 p) (opus_corr_branchQ u v (p 0) (p 1) z) := by
  classical
  let good : (Fin (q + 2) → ℕ) → Prop := fun p => p ∈ independentPrimePoolSupport
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
    (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper)
  let L : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBalancedP u v
  let R : Fin r → RowTemplate m (q + 2) := fun i => (st.shape.row i).scaleBalancedQ u v
  let I : Fin r → Prop := fun i => (L i).Parallel (R i)
  let hInv : ∀ i, I i ↔ (L i).Parallel (R i) := fun _ => Iff.rfl
  let c := chainScale S.core.parameters C a N
  let W : Fin r → ℤ → ℝ := fun i y =>
    1 + chainWeight S.core.parameters C N (st.shape.row i).anchor y
  let Ω : ℝ := ∏ i : Fin r, if hi : I i then
    W i (rowForm c (L i) p (fun k => (z k : ℚ))).num else 1
  let zP := opus_corr_branchP u v (p 0) (p 1) z
  let zQ := opus_corr_branchQ u v (p 0) (p 1) z
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
  have hdenL (i : Fin r) : (rowForm c (L i) p (fun k => (z k : ℚ))).den = 1 := hdenNew (L i)
  have hscaleDen (i : Fin r) (hi : I i) :
      (RowTemplate.parallelScaleFactor (L i) (R i) (hInv i |>.mp hi) p *
        ((rowForm c (L i) p (fun k => (z k : ℚ))).num : ℚ)).den = 1 := by
    have hPnum : ((rowForm c (L i) p (fun k => (z k : ℚ))).num : ℚ) =
        rowForm c (L i) p (fun k => (z k : ℚ)) :=
      (Rat.den_eq_one_iff _).mp (hdenL i)
    have hform := RowTemplate.rowForm_eq_monomial_scale_of_parallel c
      (L i) (R i) ((hInv i).mp hi) p hp (fun k => (z k : ℚ))
    have hval : RowTemplate.parallelScaleFactor (L i) (R i) ((hInv i).mp hi) p *
        ((rowForm c (L i) p (fun k => (z k : ℚ))).num : ℚ) =
        rowForm c (R i) p (fun k => (z k : ℚ)) := by
      rw [hPnum]
      simpa [RowTemplate.parallelScaleFactor] using hform.symm
    rw [hval]
    exact hdenNew (R i)
  have hRows := pkgMask_branchRowProductIdentity st.shape Sh' L R e hInv hrow'
    good st.rowFunction W c p hgood (fun k => (z k : ℚ)) hp hdenL hscaleDen
    (fun i => hWpos i _)
  have hformP (j : Fin r) :
      rowForm c (L j) p (fun k => (z k : ℚ)) =
        rowForm c (st.shape.row j) (dropPrimeTuple2 p) (fun k => (zP k : ℚ)) := by
    show rowForm c (L j) p _ = rowForm c (st.shape.row j) (dropPrimeTuple2 p)
      (fun k => (opus_corr_branchP u v (p 0) (p 1) z k : ℚ))
    rw [opus_corr_branchP_cast u v huv]
    exact rowForm_scaleBalancedP_tuple2 c (st.shape.row j) u v huv p z
  have hformQ (j : Fin r) :
      rowForm c (R j) p (fun k => (z k : ℚ)) =
        rowForm c (st.shape.row j) (dropPrimeTuple2 p) (fun k => (zQ k : ℚ)) := by
    show rowForm c (R j) p _ = rowForm c (st.shape.row j) (dropPrimeTuple2 p)
      (fun k => (opus_corr_branchQ u v (p 0) (p 1) z k : ℚ))
    rw [opus_corr_branchQ_cast u v huv]
    exact rowForm_scaleBalancedQ_tuple2 c (st.shape.row j) u v huv p z
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
  have hzP : Function.update (Function.update z u ((p 0 : ℤ) * z u)) v
      ((p 1 : ℤ) * Function.update z u ((p 0 : ℤ) * z u) v) = zP := by
    simp only [zP, opus_corr_branchP, Function.update_of_ne (Ne.symm huv)]
  have hzQ : Function.update (Function.update z v ((p 0 : ℤ) * z v)) u
      ((p 1 : ℤ) * Function.update z v ((p 0 : ℤ) * z v) u) = zQ := by
    simp only [zQ, opus_corr_branchQ, Function.update_of_ne huv]
  have hMasks :
      (∏ V ∈ st.masks.erase U,
        balancedBranchMaskFunction st.maskFunction u v V p (∏ k ∈ V, z k)) =
          maskP * maskQ := by
    calc
      _ = ∏ V ∈ st.masks.erase U,
          st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zP k) *
            st.maskFunction V (dropPrimeTuple2 p) (∏ k ∈ V, zQ k) := by
        apply Finset.prod_congr rfl
        intro V _
        rw [pkgMask_balancedBranchMask_substitution st.maskFunction u v V huv p z, hzP, hzQ]
      _ = maskP * maskQ := by
        simp [maskP, maskQ, Finset.prod_mul_distrib]
  change Ω *
      ((∏ V ∈ st.masks.erase U,
          balancedBranchMaskFunction st.maskFunction u v V p (∏ k ∈ V, z k)) *
        ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) =
      (maskP * rowP) * (maskQ * rowQ)
  calc
    Ω * ((∏ V ∈ st.masks.erase U,
          balancedBranchMaskFunction st.maskFunction u v V p (∏ k ∈ V, z k)) *
        ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) =
        (Ω * ∏ j : Fin r', atQ (mergedBranchRowFunction good L R e hInv
          st.rowFunction W p j) (rowForm c (Sh'.row j) p (fun k => (z k : ℚ)))) *
          (∏ V ∈ st.masks.erase U,
            balancedBranchMaskFunction st.maskFunction u v V p (∏ k ∈ V, z k)) := by ring
    _ = (rowP * rowQ) * (maskP * maskQ) := by rw [hRows', hMasks]
    _ = (maskP * rowP) * (maskQ * rowQ) := by ring

end BalancedBranches


/-! ## The second factor equals the next correlation (pointwise and averaged) -/

section BalancedNext

variable {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- An invariant row weight is unchanged by the absorption `z_u ↦ p₁p₀z_u` (04:241–247). -/
theorem opus_corr_chainWeight_absorb_eq (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (c : Fin m → ℚ) (T : RowTemplate m q)
    (p : Fin q → ℕ) (u v : Fin m) (huv : u ≠ v) (k₁ k₀ : ℕ) (z : Fin m → ℤ)
    (hcase : (u ∉ T.support ∧ v ∉ T.support) ∨ T.support = {u} ∨ T.support = {v})
    (hcu : c u ≠ 0) (hk₁ : k₁.Prime) (hk₀ : k₀.Prime)
    (hV₁ : FromArithmetic.masterScaleV S.core.parameters N C.gap < k₁)
    (hV₀ : FromArithmetic.masterScaleV S.core.parameters N C.gap < k₀)
    (hdenOld : (rowForm c T p (fun j => (z j : ℚ))).den = 1) :
    chainWeight S.core.parameters C N d
        (rowForm c T p (fun j => (Function.update z u ((k₁ : ℤ) * k₀ * z u) j : ℚ))).num =
      chainWeight S.core.parameters C N d (rowForm c T p (fun j => (z j : ℚ))).num := by
  have hcast : (fun j => (Function.update z u ((k₁ : ℤ) * k₀ * z u) j : ℚ)) =
      Function.update (fun j => (z j : ℚ)) u (((k₁ * k₀ : ℕ) : ℚ) * (z u : ℚ)) := by
    funext j
    by_cases hj : j = u
    · subst j; simp [Function.update_self]
    · simp [Function.update_of_ne hj]
  rw [hcast]
  have hu : u ∉ T.support ∨ T.support = {u} := by
    rcases hcase with ⟨hu, _⟩ | h | h
    · exact Or.inl hu
    · exact Or.inr h
    · left
      rw [h]
      simp [huv]
  rcases hu with hu | hsingle
  · rw [rowForm_update_of_not_mem_support c T p _ u _ hu]
  · rw [rowForm_update_mul_singleton c T p _ u _ hsingle hcu]
    set ℓ := rowForm c T p (fun j => (z j : ℚ))
    have hℓ : (ℓ.num : ℚ) = ℓ := (Rat.den_eq_one_iff ℓ).mp hdenOld
    have hval : ((k₁ * k₀ : ℕ) : ℚ) * ℓ = (((k₁ : ℤ) * ((k₀ : ℤ) * ℓ.num) : ℤ) : ℚ) := by
      push_cast
      rw [hℓ]
      ring
    rw [hval, Rat.num_intCast, chainWeight_mul_eq_of_prime_gt S C N d k₁ hk₁ hV₁,
      chainWeight_mul_eq_of_prime_gt S C N d k₀ hk₀ hV₀]

theorem opus_corr_extend_mem_support {q : ℕ} (lo hi : ℕ) (p : Fin q → ℕ) (k₁ k₀ : ℕ)
    (hp : p ∈ independentPrimePoolSupport (fun _ : Fin q => lo) (fun _ : Fin q => hi))
    (hk₁ : k₁ ∈ primePoolSupport lo hi) (hk₀ : k₀ ∈ primePoolSupport lo hi) :
    extendPrimeTuple (extendPrimeTuple p k₁) k₀ ∈
      independentPrimePoolSupport (fun _ : Fin (q + 2) => lo) (fun _ : Fin (q + 2) => hi) := by
  rw [independentPrimePoolSupport_mem_iff] at hp ⊢
  intro j
  refine Fin.cases ?_ (fun j' => ?_) j
  · exact hk₀
  · refine Fin.cases ?_ (fun j'' => ?_) j'
    · exact hk₁
    · exact hp j''

/-- Pointwise: after absorption, `Ω·H_{p₁}·H_{p₀}` is the next-state integrand at the extended
tuple (04:241–262). -/
theorem opus_corr_balanced_pointwise {r' : ℕ}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBalancedP u v)
      (fun i => (st.shape.row i).scaleBalancedQ u v) x.val.1 x.val.2)
    (p : Fin q → ℕ) (k₁ k₀ : ℕ) (z : Fin m → ℤ)
    (hgood : extendPrimeTuple (extendPrimeTuple p k₁) k₀ ∈ independentPrimePoolSupport
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).lower)
      (fun _ : Fin (q + 2) => (S.primeStage.pool N C.gap).upper))
    (hcu : chainScale S.core.parameters C a N u ≠ 0)
    (hcv : chainScale S.core.parameters C a N v ≠ 0)
    (hpoolLower : FromArithmetic.masterScaleV S.core.parameters N C.gap <
      (S.primeStage.pool N C.gap).lower)
    (hdenOld : ∀ (T : RowTemplate m q) (z : Fin m → ℤ),
      (rowForm (chainScale S.core.parameters C a N) T p fun k => (z k : ℚ)).den = 1)
    (hdenNew : ∀ T : RowTemplate m (q + 2),
      (rowForm (chainScale S.core.parameters C a N) T
        (extendPrimeTuple (extendPrimeTuple p k₁) k₀) fun k => (z k : ℚ)).den = 1) :
    opus_corr_balancedOmega st S C a N u v (p, Function.update z u ((k₁ : ℤ) * k₀ * z u)) *
        opus_corr_balancedResidual st S C a N U u v
          (p, Function.update z u ((k₁ : ℤ) * k₀ * z u)) k₁ *
        opus_corr_balancedResidual st S C a N U u v
          (p, Function.update z u ((k₁ : ℤ) * k₀ * z u)) k₀ =
      MaskRemovalState.pkgMask_stateIntegrand
        (pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e) S C a N
        (extendPrimeTuple (extendPrimeTuple p k₁) k₀) z := by
  classical
  set pp := extendPrimeTuple (extendPrimeTuple p k₁) k₀ with hpp
  set z' := Function.update z u ((k₁ : ℤ) * k₀ * z u) with hz'
  set c := chainScale S.core.parameters C a N with hc
  have hp0 : pp 0 = k₀ := rfl
  have hp1 : pp 1 = k₁ := rfl
  have hdrop : dropPrimeTuple2 pp = p := dropPrimeTuple2_extend p k₁ k₀
  have hslot (j : Fin (q + 2)) :
      pp j ∈ primePoolSupport (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper :=
    (independentPrimePoolSupport_mem_iff _ _ pp).mp hgood j
  have hslotFacts (j : Fin (q + 2)) := opus_corr_pool_prime_coprime S C.gap N (pp j) hpoolLower
    (hslot j)
  have hp : ∀ j, pp j ≠ 0 := fun j => (hslotFacts j).1.ne_zero
  have hk₁ : k₁.Prime := (hslotFacts 1).1
  have hk₀ : k₀.Prime := (hslotFacts 0).1
  have hV₁ : FromArithmetic.masterScaleV S.core.parameters N C.gap < k₁ := (hslotFacts 1).2.1
  have hV₀ : FromArithmetic.masterScaleV S.core.parameters N C.gap < k₀ := (hslotFacts 0).2.1
  have hcore := opus_corr_balancedBranchStateIntegrand_identity S C a N st U u v huv Sh' e hrow
    pp hgood z hp hdenNew
  rw [hdrop, hp0, hp1] at hcore
  have hP : opus_corr_balancedVec u v k₁ z' = opus_corr_branchP u v k₀ k₁ z :=
    opus_corr_balancedVec_absorb_P u v huv k₁ k₀ hk₁.ne_zero z
  have hQ : opus_corr_balancedVec u v k₀ z' = opus_corr_branchQ u v k₀ k₁ z :=
    opus_corr_balancedVec_absorb_Q u v huv k₁ k₀ hk₀.ne_zero z
  set Ω' := opus_corr_balancedOmega st S C a N u v (p, z') with hΩ'
  have hΩ'pos : 0 < Ω' :=
    lt_of_lt_of_le one_pos (opus_corr_balancedOmega_ge_one st S C a N u v (p, z'))
  have hweights :
      (∏ i : Fin r, if hi :
          ((st.shape.row i).scaleBalancedP u v).Parallel ((st.shape.row i).scaleBalancedQ u v)
          then 1 + chainWeight S.core.parameters C N (st.shape.row i).anchor
            (rowForm c ((st.shape.row i).scaleBalancedP u v) pp (fun k => (z k : ℚ))).num
          else 1) = Ω' := by
    rw [hΩ']
    unfold opus_corr_balancedOmega pkgMask_invariantRowWeight
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)
    · have hi' : opus_corr_balancedInv st u v i := hi
      rw [dif_pos hi, dif_pos hi']
      have hcase := RowTemplate.scaleBalancedBranches_parallel_support (st.shape.row i) u v huv hi
      have htuple := rowForm_scaleBalancedP_tuple2 c (st.shape.row i) u v huv pp z
      rw [hdrop, hp0, hp1] at htuple
      have hdenBr : (rowForm c (st.shape.row i) p
          (Function.update (Function.update (fun k => (z k : ℚ)) u ((k₀ : ℚ) * (z u : ℚ))) v
            ((k₁ : ℚ) * (z v : ℚ)))).den = 1 := by
        rw [← htuple]
        exact hdenNew _
      have h1 := pkgMask_chainWeight_balancedUpdate_eq S C N (st.shape.row i).anchor c
        (st.shape.row i) p u v huv k₀ k₁ z hcase hcu hcv hk₀ hk₁ hV₀ hV₁ (hdenOld _ z) hdenBr
      have h2 := opus_corr_chainWeight_absorb_eq S C N (st.shape.row i).anchor c
        (st.shape.row i) p u v huv k₁ k₀ z hcase hcu hk₁ hk₀ hV₁ hV₀ (hdenOld _ z)
      rw [htuple, h1]
      simp only [z']
      rw [h2]
    · have hi' : ¬ opus_corr_balancedInv st u v i := hi
      rw [dif_neg hi, dif_neg hi']
  rw [hweights] at hcore
  unfold opus_corr_balancedResidual
  rw [← hΩ', hP, hQ]
  field_simp
  rw [← hcore]

end BalancedNext


/-! ## The invariant-weight average (copied from lane c-mask 124a319, names `opus_corr_`) -/

theorem opus_corr_independentPrimePoolMass_eq_zero {q : ℕ} (lo hi : Fin q → ℕ)
    (p : Fin q → ℕ) (hp : p ∉ independentPrimePoolSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  have hnot : ¬ ∀ i, p i ∈ primePoolSupport (lo i) (hi i) :=
    fun hall => hp (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi'⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  exact Finset.prod_eq_zero (Finset.mem_univ i) (opus_corr_primePoolLaw_eq_zero _ _ _ hi')

theorem opus_corr_finiteIndexPrimeLaw_tsum_one {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : α → ℕ)
    (hMass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    ∑' p : α → ℕ, ∏ i, primePoolLaw (lo i) (hi i) (p i) = 1 := by
  classical
  let D : Finset (α → ℕ) := Fintype.piFinset fun i => primePoolSupport (lo i) (hi i)
  have hzero (p : α → ℕ) (hp : p ∉ D) :
      ∏ i, primePoolLaw (lo i) (hi i) (p i) = 0 := by
    have hnot : ¬ ∀ i, p i ∈ primePoolSupport (lo i) (hi i) := by
      intro hall
      apply hp
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨i, hnot_i⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (s := Finset.univ)
      (f := fun i => primePoolLaw (lo i) (hi i) (p i))
      (Finset.mem_univ i)
      (opus_corr_primePoolLaw_eq_zero (lo i) (hi i) (p i) hnot_i)
  have hcoord (i : α) :
      (∑ p ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) p) = 1 := by
    calc
      (∑ p ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) p) =
          ∑' p : ℕ, primePoolLaw (lo i) (hi i) p := by
        symm
        apply tsum_eq_sum
        intro p hp
        exact opus_corr_primePoolLaw_eq_zero (lo i) (hi i) p hp
      _ = 1 := primePoolLaw_tsum_one (lo i) (hi i) (hMass i)
  have hfinite :
      (∑ p ∈ D, ∏ i, primePoolLaw (lo i) (hi i) (p i)) = 1 := by
    calc
      (∑ p ∈ D, ∏ i, primePoolLaw (lo i) (hi i) (p i)) =
          ∏ i, ∑ p ∈ primePoolSupport (lo i) (hi i), primePoolLaw (lo i) (hi i) p := by
        unfold D
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
    (∑' p : α → ℕ, ∏ i, primePoolLaw (lo i) (hi i) (p i)) =
        ∑ p ∈ D, ∏ i, primePoolLaw (lo i) (hi i) (p i) := tsum_eq_sum (s := D) hzero
    _ = 1 := hfinite

theorem opus_corr_gapSlotAverage_restrict {K s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm)
    (l : Fin K) (N : ℕ) {q : ℕ} (ι : Fin q ↪ Fin s)
    (F : (Fin q → ℕ) → ℝ)
    (hMass : 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper) :
    gapSlotAverage S l N F =
      gapSlotAverage S l N (fun p : Fin s → ℕ => F (fun i => p (ι i))) := by
  classical
  let lo := (S.primeStage.pool N l).lower
  let hi := (S.primeStage.pool N l).upper
  let T := Finset.univ.image ι
  let Tcomp := finsetComplement T
  let enc : Fin q → T := fun i =>
    ⟨ι i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hencInj : Function.Injective enc := by
    intro i j hij
    exact ι.injective (congrArg Subtype.val hij)
  have hencSurj : Function.Surjective enc := by
    intro j
    rcases Finset.mem_image.mp j.property with ⟨i, _, h⟩
    exact ⟨i, Subtype.ext h⟩
  let eι : Fin q ≃ T := Equiv.ofBijective enc ⟨hencInj, hencSurj⟩
  let ePi : (Fin q → ℕ) ≃ (∀ j : T, ℕ) :=
    Equiv.piCongrLeft (fun _ : T => ℕ) eι
  let eSplit := piFinsetSplit T
  let eFull : ((Fin q → ℕ) × (∀ j : Tcomp, ℕ)) ≃ (Fin s → ℕ) :=
    (Equiv.prodCongr ePi (Equiv.refl _)).trans eSplit.symm
  let Pq := independentPrimePoolSupport (fun _ : Fin q => lo) (fun _ => hi)
  let Ps := independentPrimePoolSupport (fun _ : Fin s => lo) (fun _ => hi)
  let Pc := Fintype.piFinset fun j : Tcomp => primePoolSupport lo hi
  let μc : (∀ j : Tcomp, ℕ) → ℝ := fun r => ∏ j, primePoolLaw lo hi (r j)
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
      by_cases hiT : i ∈ T
      · exact Finset.mem_union.mpr (Or.inl hiT)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiT⟩))
  have hsplit (p : Fin q → ℕ) (r : ∀ j : Tcomp, ℕ) :
      eSplit (eFull (p, r)) = (ePi p, r) := by
    simp [eFull]
  have hselected (p : Fin q → ℕ) (r : ∀ j : Tcomp, ℕ) (i : Fin q) :
      eFull (p, r) (ι i) = p i := by
    let j : T := enc i
    calc
      eFull (p, r) (ι i) = (eSplit (eFull (p, r))).1 j :=
        (piFinsetSplit_left_apply T (eFull (p, r)) j).symm
      _ = (ePi p) j := by rw [hsplit]
      _ = p i := by
        change (Equiv.piCongrLeft (fun _ : T => ℕ) eι) p (eι i) = p i
        simp [Equiv.piCongrLeft]
  have hcomplement (p : Fin q → ℕ) (r : ∀ j : Tcomp, ℕ) (j : Tcomp) :
      eFull (p, r) j.val = r j := by
    calc
      eFull (p, r) j.val = (eSplit (eFull (p, r))).2 j :=
        (piFinsetSplit_right_apply T (eFull (p, r)) j).symm
      _ = r j := by rw [hsplit]
  have hmassFactor (p : Fin q → ℕ) (r : ∀ j : Tcomp, ℕ) :
      gapSlotMass S l N (eFull (p, r)) = gapSlotMass S l N p * μc r := by
    change independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi) (eFull (p, r)) =
      independentPrimePoolMass (fun _ : Fin q => lo) (fun _ => hi) p * μc r
    unfold independentPrimePoolMass
    have hTprod :
        (∏ j : T, primePoolLaw lo hi (eFull (p, r) j.val)) =
          ∏ i : Fin q, primePoolLaw lo hi (p i) := by
      symm
      apply Finset.prod_bij (fun i _ => enc i)
      · intro i hiI
        exact Finset.mem_univ _
      · intro i hiI j hj hEq
        exact hencInj hEq
      · intro j hj
        exact ⟨eι.symm j, Finset.mem_univ _, by
          change eι (eι.symm j) = j
          exact eι.apply_symm_apply j⟩
      · intro i hiI
        rw [hselected]
    have hCprod :
        (∏ j : Tcomp, primePoolLaw lo hi (eFull (p, r) j.val)) = μc r := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hcomplement]
    have hTattach :
        (∏ i ∈ T, primePoolLaw lo hi (eFull (p, r) i)) =
          ∏ j : T, primePoolLaw lo hi (eFull (p, r) j.val) := by
      simpa using (Finset.prod_attach T
        (fun i => primePoolLaw lo hi (eFull (p, r) i))).symm
    have hCattach :
        (∏ i ∈ Tcomp, primePoolLaw lo hi (eFull (p, r) i)) =
          ∏ j : Tcomp, primePoolLaw lo hi (eFull (p, r) j.val) := by
      simpa using (Finset.prod_attach Tcomp
        (fun i => primePoolLaw lo hi (eFull (p, r) i))).symm
    calc
      (∏ i : Fin s, primePoolLaw lo hi (eFull (p, r) i)) =
          ∏ i ∈ Finset.univ, primePoolLaw lo hi (eFull (p, r) i) := by simp
      _ = ∏ i ∈ T ∪ Tcomp, primePoolLaw lo hi (eFull (p, r) i) := by rw [hunion]
      _ = (∏ i ∈ T, primePoolLaw lo hi (eFull (p, r) i)) *
          ∏ i ∈ Tcomp, primePoolLaw lo hi (eFull (p, r) i) := Finset.prod_union hdisj
      _ = (∏ j : T, primePoolLaw lo hi (eFull (p, r) j.val)) *
          ∏ j : Tcomp, primePoolLaw lo hi (eFull (p, r) j.val) := by
        rw [hTattach, hCattach]
      _ = _ := by rw [hTprod, hCprod]
  have hmassFactorInd (p : Fin q → ℕ) (r : ∀ j : Tcomp, ℕ) :
      independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi) (eFull (p, r)) =
        gapSlotMass S l N p * μc r := by
    simpa [gapSlotMass] using hmassFactor p r
  have hqzero (p : Fin q → ℕ) (hp : p ∉ Pq) : gapSlotMass S l N p = 0 := by
    simpa [Pq, gapSlotMass] using
      opus_corr_independentPrimePoolMass_eq_zero
        (fun _ : Fin q => lo) (fun _ => hi) p hp
  have hczero (r : ∀ j : Tcomp, ℕ) (hr : r ∉ Pc) : μc r = 0 := by
    have hnot : ¬ ∀ j : Tcomp, r j ∈ primePoolSupport lo hi := by
      intro hall
      apply hr
      exact Fintype.mem_piFinset.mpr hall
    obtain ⟨j, hnotJ⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (s := Finset.univ) (f := fun j => primePoolLaw lo hi (r j))
      (Finset.mem_univ j) (opus_corr_primePoolLaw_eq_zero lo hi (r j) hnotJ)
  have hczeroSum : (∑ r ∈ Pc, μc r) = 1 := by
    calc
      (∑ r ∈ Pc, μc r) = ∑' r : ∀ j : Tcomp, ℕ, μc r :=
        (tsum_eq_sum (s := Pc) hczero).symm
      _ = 1 := opus_corr_finiteIndexPrimeLaw_tsum_one
        (fun _ : Tcomp => lo) (fun _ => hi) (fun _ => hMass)
  have hpairZero (x : (Fin q → ℕ) × (∀ j : Tcomp, ℕ)) (hx : x ∉ Pq ×ˢ Pc) :
      (gapSlotMass S l N x.1 * μc x.2) * F x.1 = 0 := by
    have hx' : x.1 ∉ Pq ∨ x.2 ∉ Pc := by
      by_contra h
      push_neg at h
      exact hx (Finset.mem_product.mpr h)
    rcases hx' with hp | hr
    · simp [hqzero x.1 hp]
    · simp [hczero x.2 hr]
  have hfullSum :
      gapSlotAverage S l N (fun p : Fin s → ℕ => F (fun i => p (ι i))) =
        ∑' x : (Fin q → ℕ) × (∀ j : Tcomp, ℕ),
          (gapSlotMass S l N x.1 * μc x.2) * F x.1 := by
    unfold gapSlotAverage
    calc
      (∑' p : Fin s → ℕ,
          independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi) p *
            F (fun i => p (ι i))) =
        ∑' x : (Fin q → ℕ) × (∀ j : Tcomp, ℕ),
          independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi)
            (eFull x) * F (fun i => eFull x (ι i)) := by
        symm
        exact eFull.tsum_eq (fun p =>
          independentPrimePoolMass (fun _ : Fin s => lo) (fun _ => hi) p *
            F (fun i => p (ι i)))
      _ = _ := by
        apply tsum_congr
        intro x
        rw [hmassFactorInd]
        congr 1
        congr 1
        funext i
        exact hselected x.1 x.2 i
  have hpairSum :
      (∑' x : (Fin q → ℕ) × (∀ j : Tcomp, ℕ),
          (gapSlotMass S l N x.1 * μc x.2) * F x.1) = gapSlotAverage S l N F := by
    calc
      _ = ∑ x ∈ Pq ×ˢ Pc, (gapSlotMass S l N x.1 * μc x.2) * F x.1 :=
        tsum_eq_sum (s := Pq ×ˢ Pc) hpairZero
      _ = ∑ p ∈ Pq, ∑ r ∈ Pc,
          (gapSlotMass S l N p * μc r) * F p := by
        exact Finset.sum_product' Pq Pc
          (fun p r => (gapSlotMass S l N p * μc r) * F p)
      _ = ∑ p ∈ Pq, ∑ r ∈ Pc,
          (gapSlotMass S l N p * F p) * μc r := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = ∑ p ∈ Pq, (gapSlotMass S l N p * F p) * ∑ r ∈ Pc, μc r := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
      _ = ∑ p ∈ Pq, gapSlotMass S l N p * F p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hczeroSum]
        ring
      _ = gapSlotAverage S l N F := by
        unfold gapSlotAverage
        symm
        exact tsum_eq_sum (s := Pq) (fun p hp => by simp [hqzero p hp])
  exact (hfullSum.trans hpairSum).symm

theorem opus_corr_prod_one_add_eq_sum_powerset {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → ℝ) :
    (∏ i ∈ A, (1 + f i)) = ∑ J ∈ A.powerset, ∏ i ∈ J, f i := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_powerset_insert ha, ih]
    have hterms : ∀ J ∈ A.powerset,
        (∏ i ∈ insert a J, f i) = f a * ∏ i ∈ J, f i := by
      intro J hJ
      have hnot : a ∉ J := fun hmem => ha ((Finset.mem_powerset.mp hJ) hmem)
      rw [Finset.prod_insert hnot]
    rw [Finset.mul_sum]
    calc
      (∑ J ∈ A.powerset, (1 + f a) * ∏ i ∈ J, f i) =
          ∑ J ∈ A.powerset,
            (∏ i ∈ J, f i + ∏ i ∈ insert a J, f i) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hterms J hJ]
        ring
      _ = _ := Finset.sum_add_distrib

theorem opus_corr_stateRowWeightAverage_eq_maskRowSubsetAverage_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (J : Finset (Fin r)) :
    ∀ᶠ N in atTop,
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ),
        gapPivotMass S C N x.1 x.2 *
          ∏ R ∈ J,
            chainWeight S.core.parameters C N (Sh.row R).anchor
              (rowForm (chainScale S.core.parameters C a N) (Sh.row R) x.1
                (fun k => (x.2 k : ℚ))).num) =
        maskRowSubsetAverage S C a N Sh ι J := by
  have hMass := primePoolMass_pos_eventually S C.gap
  have hden := rowForm_den_one_eventually (q := q) S C a ha
  filter_upwards [hMass, hden] with N hMass hden
  let G : (Fin q → ℕ) × (Fin m → ℤ) → ℝ := fun x =>
    ∏ R ∈ J,
      chainWeight S.core.parameters C N (Sh.row R).anchor
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) x.1
          (fun k => (x.2 k : ℚ))).num
  let Fq : (Fin q → ℕ) → ℝ := fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z * G (p, z)
  let Fs : (Fin s → ℕ) → ℝ := fun p =>
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R ∈ J,
        atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ)))
  have hjoint :
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x) =
        gapSlotAverage S C.gap N Fq := by
    symm
    exact pkgMask_gapPivotTsum_fubini S C N G
  have hrowAt (p : Fin s → ℕ) (z : Fin m → ℤ) (R : Fin r) :
      atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ))) =
        chainWeight S.core.parameters C N (Sh.row R).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
    have hd := hden (Sh.row R) (fun i => p (ι i)) z
    simp [atQ, hd]
  have hFs : Fs = fun p => Fq (fun i => p (ι i)) := by
    funext p
    dsimp [Fs, Fq]
    apply tsum_congr
    intro z
    congr 1
    apply Finset.prod_congr rfl
    intro R hR
    exact hrowAt p z R
  calc
    (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * G x) =
        gapSlotAverage S C.gap N Fq := hjoint
    _ = gapSlotAverage S C.gap N Fs := by
        rw [opus_corr_gapSlotAverage_restrict S C.gap N ι Fq hMass, hFs]
    _ = maskRowSubsetAverage S C a N Sh ι J := by rfl

theorem opus_corr_invariantRowWeight_average_le_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (ι : Fin q ↪ Fin s)
    (hlisted : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ι P ∈ Dm)
    (I : Fin r → Prop) :
    ∀ᶠ N in atTop,
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        pkgMask_invariantRowWeight
          (⟨Sh, ∅, (fun _ _ _ => 1), (fun _ _ _ => 1)⟩ : MaskRemovalState m q r)
          S C a N I x.1 x.2) ≤ (2 : ℝ) ^ (r + 1) := by
  classical
  let st : MaskRemovalState m q r :=
    ⟨Sh, ∅, (fun _ _ _ => 1), (fun _ _ _ => 1)⟩
  let Iset : Finset (Fin r) := Finset.univ.filter I
  let Pset := Iset.powerset
  let rowTerm (N : ℕ) (J : Finset (Fin r)) (x : (Fin q → ℕ) × (Fin m → ℤ)) : ℝ :=
    ∏ R ∈ J,
      chainWeight S.core.parameters C N (Sh.row R).anchor
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) x.1
          (fun k => (x.2 k : ℚ))).num
  let rowAverage (N : ℕ) (J : Finset (Fin r)) : ℝ :=
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 * rowTerm N J x
  have hJevent : ∀ᶠ N in atTop, ∀ J : Finset (Fin r),
      J ⊆ Iset → maskRowSubsetAverage S C a N Sh ι J ≤ 2 := by
    apply Filter.eventually_all.2
    intro J
    filter_upwards [maskRowSubsetAverage_le_two_eventually S C a ha Sh ι hlisted J] with N hN
    intro hJ
    exact hN
  have haverageEq : ∀ J : Finset (Fin r),
      ∀ᶠ N in atTop, rowAverage N J = maskRowSubsetAverage S C a N Sh ι J := by
    intro J
    simpa [rowAverage, rowTerm, st] using
      (opus_corr_stateRowWeightAverage_eq_maskRowSubsetAverage_eventually
        S C a ha Sh ι hlisted J)
  have hweightExpand (N : ℕ) (x : (Fin q → ℕ) × (Fin m → ℤ)) :
      pkgMask_invariantRowWeight st S C a N I x.1 x.2 =
        ∑ J ∈ Pset, rowTerm (N := N) J x := by
    unfold pkgMask_invariantRowWeight
    have hfilter :
        (∏ i : Fin r, if hi : I i then
          1 + chainWeight S.core.parameters C N (Sh.row i).anchor
            (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
              (fun k => (x.2 k : ℚ))).num else 1) =
          ∏ i ∈ Iset,
            (1 + chainWeight S.core.parameters C N (Sh.row i).anchor
              (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
                (fun k => (x.2 k : ℚ))).num) := by
      change (∏ i ∈ (Finset.univ : Finset (Fin r)), if I i then
        1 + chainWeight S.core.parameters C N (Sh.row i).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
            (fun k => (x.2 k : ℚ))).num else 1) = _
      rw [← Finset.prod_filter (s := (Finset.univ : Finset (Fin r))) I
        (fun i => 1 + chainWeight S.core.parameters C N (Sh.row i).anchor
          (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
            (fun k => (x.2 k : ℚ))).num)]
    rw [hfilter]
    exact opus_corr_prod_one_add_eq_sum_powerset Iset
      (fun i => chainWeight S.core.parameters C N (Sh.row i).anchor
        (rowForm (chainScale S.core.parameters C a N) (Sh.row i) x.1
          (fun k => (x.2 k : ℚ))).num)
  have hfinite (N : ℕ) :
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        pkgMask_invariantRowWeight st S C a N I x.1 x.2) =
        ∑ J ∈ Pset, rowAverage (N := N) J := by
    let D := gapPivotSupport (q := q) S C N
    have hzero (x : (Fin q → ℕ) × (Fin m → ℤ)) (hx : x ∉ D) :
        gapPivotMass S C N x.1 x.2 *
          pkgMask_invariantRowWeight st S C a N I x.1 x.2 = 0 := by
      rw [opus_corr_gapPivotMass_eq_zero S C N x hx]
      simp
    have hzeroJ (J : Finset (Fin r)) (x : (Fin q → ℕ) × (Fin m → ℤ))
        (hx : x ∉ D) : gapPivotMass S C N x.1 x.2 * rowTerm (N := N) J x = 0 := by
      rw [opus_corr_gapPivotMass_eq_zero S C N x hx]
      simp
    calc
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          pkgMask_invariantRowWeight st S C a N I x.1 x.2) =
          ∑ x ∈ D, gapPivotMass S C N x.1 x.2 *
            pkgMask_invariantRowWeight st S C a N I x.1 x.2 :=
        tsum_eq_sum (s := D) hzero
      _ = ∑ x ∈ D, ∑ J ∈ Pset,
            gapPivotMass S C N x.1 x.2 * rowTerm (N := N) J x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hweightExpand N x, Finset.mul_sum]
      _ = ∑ J ∈ Pset, ∑ x ∈ D,
            gapPivotMass S C N x.1 x.2 * rowTerm (N := N) J x := by
        rw [Finset.sum_comm]
      _ = ∑ J ∈ Pset, rowAverage (N := N) J := by
        apply Finset.sum_congr rfl
        intro J hJ
        unfold rowAverage
        symm
        exact tsum_eq_sum (s := D) (hzeroJ J)
  filter_upwards [hJevent, Filter.eventually_all.2 haverageEq] with N havg heq
  have hterms : ∀ J ∈ Pset, rowAverage (N := N) J ≤ 2 := by
    intro J hJ
    have hsub : J ⊆ Iset := Finset.mem_powerset.mp hJ
    rw [heq J]
    exact havg J hsub
  have hsumle : ∑ J ∈ Pset, rowAverage (N := N) J ≤ ∑ J ∈ Pset, (2 : ℝ) :=
    Finset.sum_le_sum hterms
  have hcard : Iset.card ≤ r := by
    simpa [Iset] using
      (Finset.card_le_card (Finset.filter_subset I (Finset.univ : Finset (Fin r))))
  have hpower : (2 : ℝ) * (2 : ℝ) ^ Iset.card ≤ (2 : ℝ) ^ (r + 1) := by
    rw [pow_succ]
    have hpowNat : (2 : ℝ) ^ Iset.card ≤ (2 : ℝ) ^ r := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega) hcard)
    nlinarith [hpowNat]
  have hsumConst : ∑ J ∈ Pset, (2 : ℝ) = (2 : ℝ) * (2 : ℝ) ^ Iset.card := by
    calc
      ∑ J ∈ Pset, (2 : ℝ) = (Pset.card : ℝ) * 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (2 : ℝ) * (2 : ℝ) ^ Iset.card := by
        simp [Pset, Finset.card_powerset]
        ring
  rw [hfinite]
  exact hsumle.trans (hsumConst ▸ hpower)



/-! ## Assembly of the balanced step -/

section BalancedAssembly

variable {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}

/-- The absorbed second factor is exactly the correlation of the next state. -/
theorem opus_corr_balanced_second_factor_eq {r' : ℕ}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (N : ℕ) (st : MaskRemovalState m q r) (U : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v)
    (Sh' : RowShape m (q + 2) r')
    (e : RowBranchIndex (fun i =>
      ((st.shape.row i).scaleBalancedP u v).Parallel
        ((st.shape.row i).scaleBalancedQ u v)) ≃ Fin r')
    (hrow : ∀ x, Sh'.row (e x) = RowBranchTemplate st.shape
      (fun i => (st.shape.row i).scaleBalancedP u v)
      (fun i => (st.shape.row i).scaleBalancedQ u v) x.val.1 x.val.2)
    (hcu : chainScale S.core.parameters C a N u ≠ 0)
    (hcv : chainScale S.core.parameters C a N v ≠ 0)
    (hpoolLower : FromArithmetic.masterScaleV S.core.parameters N C.gap <
      (S.primeStage.pool N C.gap).lower)
    (hdenOld : ∀ (T : RowTemplate m q) (p : Fin q → ℕ) (z : Fin m → ℤ),
      (rowForm (chainScale S.core.parameters C a N) T p fun k => (z k : ℚ)).den = 1)
    (hdenNew : ∀ (T : RowTemplate m (q + 2)) (p : Fin (q + 2) → ℕ) (z : Fin m → ℤ),
      (rowForm (chainScale S.core.parameters C a N) T p fun k => (z k : ℚ)).den = 1) :
    ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        ∑' kk : ℕ × ℕ, (primePoolLaw (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper kk.1 *
          primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper kk.2) *
          (opus_corr_balancedOmega st S C a N u v
              (x.1, Function.update x.2 u ((kk.1 : ℤ) * kk.2 * x.2 u)) *
            opus_corr_balancedResidual st S C a N U u v
              (x.1, Function.update x.2 u ((kk.1 : ℤ) * kk.2 * x.2 u)) kk.1 *
            opus_corr_balancedResidual st S C a N U u v
              (x.1, Function.update x.2 u ((kk.1 : ℤ) * kk.2 * x.2 u)) kk.2) =
      (pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation S C a N := by
  classical
  set st' := pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e with hst'
  set lo := (S.primeStage.pool N C.gap).lower
  set hi := (S.primeStage.pool N C.gap).upper
  have hre := pkgMask_gapPivot_freshPair_reindex S C N (fun w =>
    MaskRemovalState.pkgMask_stateIntegrand st' S C a N
      (pkgMask_oldFreshPairEquiv w).1 (pkgMask_oldFreshPairEquiv w).2)
  simp only [Equiv.apply_symm_apply] at hre
  rw [MaskRemovalState.pkgMask_stateCorrelation_joint st' S C a N]
  calc
    _ = ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
          ∑' kk : ℕ × ℕ, (primePoolLaw lo hi kk.1 * primePoolLaw lo hi kk.2) *
            MaskRemovalState.pkgMask_stateIntegrand st' S C a N
              (pkgMask_oldFreshPairEquiv (x, kk)).1 (pkgMask_oldFreshPairEquiv (x, kk)).2 := by
      apply tsum_congr
      intro x
      by_cases hx : x.1 ∈ independentPrimePoolSupport (fun _ : Fin q => lo) (fun _ : Fin q => hi)
      · congr 1
        apply tsum_congr
        intro kk
        by_cases hk : kk.1 ∈ primePoolSupport lo hi ∧ kk.2 ∈ primePoolSupport lo hi
        · congr 1
          exact opus_corr_balanced_pointwise S C a N st U u v huv Sh' e hrow x.1 kk.1 kk.2 x.2
            (opus_corr_extend_mem_support lo hi x.1 kk.1 kk.2 hx hk.1 hk.2) hcu hcv hpoolLower
            (fun T z => hdenOld T x.1 z) (fun T => hdenNew T _ x.2)
        · rcases not_and_or.mp hk with h | h
          · rw [opus_corr_primePoolLaw_eq_zero lo hi _ h]; ring
          · rw [opus_corr_primePoolLaw_eq_zero lo hi _ h]; ring
      · rw [opus_corr_gapPivotMass_eq_zero S C N x
          (fun hmem => hx (Finset.mem_product.mp hmem).1)]
        ring
    _ = _ := hre

/-- The balanced step of Lemma `lem:mask-removal` (04:176–297): the full statement of
`opus_corr_mask_step_balanced`. -/
theorem opus_corr_mask_step_balanced_proof {m q r : ℕ} (Jstar : Finset (Fin m))
    (hJ : 2 ≤ Jstar.card) (Sh : RowShape m q r) (hStar : (Sh.row Sh.star).support = Jstar)
    (masks : Finset (Finset (Fin m))) (U : Finset (Fin m)) (hU : U ∈ masks)
    (hJU : Jstar ⊆ U) (u v : Fin m) (huJ : u ∈ Jstar) (hvJ : v ∈ Jstar) (huv : u ≠ v) :
    ∃ (r' : ℕ) (Sh' : RowShape m (q + 2) r') (tests : Finset (IntegerPolynomial (q + 2)))
      (C₁ : ℝ),
      r' ≤ 2 * r ∧ (Sh'.row Sh'.star).support = Jstar ∧ (∀ P ∈ tests, P ≠ 0) ∧ 0 < C₁ ∧
      ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
        (S : FromArithmetic.MasterScales K Aset s Dm) (ι : Fin (q + 2) ↪ Fin s),
        TestsListed Dm ι tests →
      ∀ (C : MasterChain K m) (a : Fin m → ℚ), (∀ d, a d ∈ Aset) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ (st : MaskRemovalState m q r) (gstar : ℤ → ℝ),
          st.shape = Sh → st.masks = masks → st.Valid S C a N Jstar gstar →
          ∃ st' : MaskRemovalState m (q + 2) r',
            st'.shape = Sh' ∧ st'.masks = masks.erase U ∧ st'.Valid S C a N Jstar gstar ∧
            |st.correlation S C a N| ^ 2 ≤ C₁ * |st'.correlation S C a N| + ε := by
  classical
  have huS : u ∈ (Sh.row Sh.star).support := by rw [hStar]; exact huJ
  have hvS : v ∈ (Sh.row Sh.star).support := by rw [hStar]; exact hvJ
  obtain ⟨r', Sh', e, hrow, hr', hstar', hstarIndex⟩ :=
    exists_scaleBalanced_row_shape Sh Jstar hStar u v huS hvS huv
  let emb : Fin q → Fin (q + 2) := Fin.castAdd 2
  have hemb : Function.Injective emb := Fin.castAdd_injective q 2
  refine ⟨r', Sh', (templateMinors Sh).image (MvPolynomial.rename emb), (2 : ℝ) ^ (r + 2),
    hr', hstar', ?_, by positivity, ?_⟩
  · intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    intro hzero
    apply (Finset.mem_filter.mp hP₀).2
    apply MvPolynomial.rename_injective emb hemb
    simpa using hzero
  intro K s Aset Dm S ι hlisted C a ha ε hε
  let ιold : Fin q ↪ Fin s := ⟨fun i => ι (emb i), fun i j h => hemb (ι.injective h)⟩
  have hlistedOld : ∀ P, P ∈ templateMinors Sh → MvPolynomial.rename ιold P ∈ Dm := by
    intro P hP
    have h := hlisted _ (Finset.mem_image_of_mem (MvPolynomial.rename emb) hP)
    rw [MvPolynomial.rename_rename] at h
    exact h
  let δ₁ : ℝ := min 1 (ε / 4)
  have hδ₁ : 0 < δ₁ := lt_min one_pos (by positivity)
  let δ₂ : ℝ := ε / (2 * (2 : ℝ) ^ (r + 2))
  have hδ₂ : 0 < δ₂ := by positivity
  filter_upwards [opus_corr_balanced_insertion_estimate S C u v huv (2 * r) δ₁ hδ₁,
    opus_corr_absorption_estimate S C u (4 * r) δ₂ hδ₂,
    opus_corr_invariantRowWeight_average_le_eventually S C a ha Sh ιold hlistedOld
      (fun i => ((Sh.row i).scaleBalancedP u v).Parallel ((Sh.row i).scaleBalancedQ u v)),
    primePoolMass_pos_eventually S C.gap, pool_lower_gt_masterScaleV_eventually S C.gap,
    chainScale_pos_eventually S C a ha, rowForm_den_one_eventually (q := q) S C a ha,
    rowForm_den_one_eventually (q := q + 2) S C a ha]
    with N hIns hAbs hFirst hMass hpoolLower hcpos hdenOld hdenNew
  intro st gstar hsh hmasks hvalid
  subst hsh
  have hU' : U ∈ st.masks := by rw [hmasks]; exact hU
  have hu : u ∈ U := hJU huJ
  have hv : v ∈ U := hJU hvJ
  have hstarNot := RowTemplate.scaleBalanced_not_parallel (st.shape.row st.shape.star) u v huv
    huS hvS
  refine ⟨pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e, rfl, ?_,
    pkgMask_balancedBranchMaskRemovalState_valid S C a N st U u v huv Jstar gstar hvalid Sh' e
      hrow hstarIndex hstarNot hpoolLower, ?_⟩
  · show st.masks.erase U = masks.erase U
    rw [hmasks]
  set V : ℝ := (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) with hVdef
  -- the insertion
  have hΦ : ∀ x : (Fin q → ℕ) × (Fin m → ℤ),
      |MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1 x.2| ≤ V ^ (2 * r) :=
    fun x => MaskRemovalState.pkgMask_stateIntegrand_abs_le st S C a N Jstar gstar hvalid x.1 x.2
  have h1 := hIns q (fun x => MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1 x.2) hΦ
  dsimp only at h1
  have hcorr : st.correlation S C a N = ∑' x : (Fin q → ℕ) × (Fin m → ℤ),
      gapPivotMass S C N x.1 x.2 * MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1 x.2 :=
    MaskRemovalState.pkgMask_stateCorrelation_joint st S C a N
  set I₂ := ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
    poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
      MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1
        (opus_corr_balancedVec u v k x.2)) with hI₂
  -- Cauchy–Schwarz
  have h2 := opus_corr_balanced_cs st S C a N Jstar gstar hvalid hMass U u v huv hU' hu hv
  set EΩ := ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
    opus_corr_balancedOmega st S C a N u v x with hEΩ
  set SF := ∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
    (opus_corr_balancedOmega st S C a N u v x *
      (poolAverage S C.gap N (fun k => opus_corr_eta k (x.2 u) *
        opus_corr_balancedResidual st S C a N U u v x k)) ^ 2) with hSF
  have hΩnn : ∀ x, 0 ≤ opus_corr_balancedOmega st S C a N u v x := fun x =>
    le_trans zero_le_one (opus_corr_balancedOmega_ge_one st S C a N u v x)
  have hEΩnn : 0 ≤ EΩ := tsum_nonneg fun x =>
    mul_nonneg (gapPivotMass_nonneg S C N hMass x.1 x.2) (hΩnn x)
  have hSFnn : 0 ≤ SF := tsum_nonneg fun x =>
    mul_nonneg (gapPivotMass_nonneg S C N hMass x.1 x.2)
      (mul_nonneg (hΩnn x) (sq_nonneg _))
  have h3 : EΩ ≤ (2 : ℝ) ^ (r + 1) := hFirst
  -- the second factor
  have hG : ∀ (k₁ k₀ : ℕ) (x : (Fin q → ℕ) × (Fin m → ℤ)),
      |opus_corr_balancedOmega st S C a N u v x *
          opus_corr_balancedResidual st S C a N U u v x k₁ *
          opus_corr_balancedResidual st S C a N U u v x k₀| ≤ V ^ (4 * r) := by
    intro k₁ k₀ x
    have hval := opus_corr_eraseMask_valid st S C a N Jstar gstar U hvalid
    have hA₁ := MaskRemovalState.pkgMask_stateIntegrand_abs_le (opus_corr_eraseMask st U)
      S C a N Jstar gstar hval x.1 (opus_corr_balancedVec u v k₁ x.2)
    have hA₀ := MaskRemovalState.pkgMask_stateIntegrand_abs_le (opus_corr_eraseMask st U)
      S C a N Jstar gstar hval x.1 (opus_corr_balancedVec u v k₀ x.2)
    have hΩ1 := opus_corr_balancedOmega_ge_one st S C a N u v x
    have hΩpos : 0 < opus_corr_balancedOmega st S C a N u v x := lt_of_lt_of_le one_pos hΩ1
    unfold opus_corr_balancedResidual
    set Ω := opus_corr_balancedOmega st S C a N u v x
    set A₁ := MaskRemovalState.pkgMask_stateIntegrand (opus_corr_eraseMask st U) S C a N x.1
      (opus_corr_balancedVec u v k₁ x.2)
    set A₀ := MaskRemovalState.pkgMask_stateIntegrand (opus_corr_eraseMask st U) S C a N x.1
      (opus_corr_balancedVec u v k₀ x.2)
    have heq : Ω * (A₁ / Ω) * (A₀ / Ω) = (A₁ * A₀) / Ω := by
      field_simp
    rw [heq, abs_div, abs_of_pos hΩpos, abs_mul, div_le_iff₀ hΩpos]
    have hV0 : 0 ≤ V ^ (2 * r) := le_trans (abs_nonneg _) hA₁
    calc
      |A₁| * |A₀| ≤ V ^ (2 * r) * V ^ (2 * r) :=
        mul_le_mul hA₁ hA₀ (abs_nonneg _) hV0
      _ = V ^ (4 * r) * 1 := by ring
      _ ≤ V ^ (4 * r) * Ω := mul_le_mul_of_nonneg_left hΩ1 (by positivity)
  have h4 := opus_corr_balanced_square_expand st S C a N U u v
  have h5 := hAbs q (fun k₁ k₀ x => opus_corr_balancedOmega st S C a N u v x *
      opus_corr_balancedResidual st S C a N U u v x k₁ *
      opus_corr_balancedResidual st S C a N U u v x k₀) hG
  have h6 := opus_corr_balanced_second_factor_eq S C a N st U u v huv Sh' e hrow
    (hcpos u).ne' (hcpos v).ne' hpoolLower hdenOld hdenNew
  have h5' : |SF - (pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation
      S C a N| ≤ δ₂ := by
    rw [hSF, h4, ← h6]
    exact h5
  have hSFle : SF ≤ |(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation
      S C a N| + δ₂ := by
    have := (abs_le.mp h5').2
    have := le_abs_self ((pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation
      S C a N)
    linarith
  -- combine
  have hI₂sq : |I₂| ^ 2 ≤ (2 : ℝ) ^ (r + 1) * (|(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation S C a N| + δ₂) := by
    calc
      |I₂| ^ 2 ≤ EΩ * SF := h2
      _ ≤ (2 : ℝ) ^ (r + 1) * SF := mul_le_mul_of_nonneg_right h3 hSFnn
      _ ≤ (2 : ℝ) ^ (r + 1) * (|(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation S C a N| + δ₂) :=
        mul_le_mul_of_nonneg_left hSFle (by positivity)
  have hcorrle : |st.correlation S C a N| ≤ |I₂| + δ₁ := by
    rw [hcorr]
    have := abs_sub_abs_le_abs_sub
      (∑' x : (Fin q → ℕ) × (Fin m → ℤ), gapPivotMass S C N x.1 x.2 *
        MaskRemovalState.pkgMask_stateIntegrand st S C a N x.1 x.2) I₂
    linarith
  have hsq : |st.correlation S C a N| ^ 2 ≤ (|I₂| + δ₁) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hcorrle 2
  have hδ₁le : δ₁ ≤ 1 := min_le_left _ _
  have hδ₁le' : δ₁ ≤ ε / 4 := min_le_right _ _
  have hδ₂eq : (2 : ℝ) ^ (r + 2) * δ₂ = ε / 2 := by
    show (2 : ℝ) ^ (r + 2) * (ε / (2 * (2 : ℝ) ^ (r + 2))) = ε / 2
    rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hpow : (2 : ℝ) ^ (r + 2) = 2 * (2 : ℝ) ^ (r + 1) := by ring
  have hδ₁sq : δ₁ ^ 2 ≤ ε / 4 := by nlinarith
  have e1 := opus_corr_sq_add_le |I₂| δ₁
  have e2 : 2 * |I₂| ^ 2 ≤ (2 : ℝ) ^ (r + 2) *
      |(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation S C a N| +
        ε / 2 := by
    calc
      2 * |I₂| ^ 2 ≤ 2 * ((2 : ℝ) ^ (r + 1) *
          (|(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation
            S C a N| + δ₂)) := by linarith
      _ = (2 : ℝ) ^ (r + 2) *
          |(pkgMask_balancedBranchMaskRemovalState S C N st U u v huv Sh' e).correlation
            S C a N| + (2 : ℝ) ^ (r + 2) * δ₂ := by rw [hpow]; ring
      _ = _ := by rw [hδ₂eq]
  linarith

end BalancedAssembly

end
end HindmanSumsProducts
