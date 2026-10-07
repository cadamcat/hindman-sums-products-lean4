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

end
end HindmanSumsProducts
