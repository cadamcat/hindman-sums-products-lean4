import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside
import HindmanSumsProducts.Correlation.PkgMask

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
theorem opus_corr_power_step {X y z A B e₁ e₂ : ℝ} (k : ℕ) (hX : 0 ≤ X) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (he₁ : 0 ≤ e₁)
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
      · have hpow := opus_corr_power_step rest.length (abs_nonneg _) (abs_nonneg _)
          hCm.le hε₁.le hineq hineq'
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

end
end HindmanSumsProducts
