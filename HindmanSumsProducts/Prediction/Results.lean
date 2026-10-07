import HindmanSumsProducts.Prediction.Outside
import HindmanSumsProducts.CubeCornerCharted
import HindmanSumsProducts.Prediction.PkgB
import HindmanSumsProducts.Prediction.PkgC
import HindmanSumsProducts.Prediction.PkgD
import HindmanSumsProducts.Prediction.PkgB2
import HindmanSumsProducts.Prediction.PkgOpusDpo
import HindmanSumsProducts.Prediction.PkgDFlat
import HindmanSumsProducts.Prediction.PkgDPre

/-!
# Dual-test pseudorandomness, bounded dense models, nilsequence testing (§5.1–§5.2)

`05_prediction.tex` 63–353.  Throughout, `MS : MasterScales K As sl Dm` are §3's master scales and
`A = MS.core.parameters`.  "`o(1)` uniformly over the inputs" is `∀ ε > 0, ∀ᶠ N in atTop, ∀ inputs`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl r : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-! ### Lemma `lem:dual-pseudorandomness` (05:68–190) -/

/-- `A_* = 2^{2^{d_*} − 1}` (05:76). -/
def dualMomentConstant (dStar : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ dStar - 1)

/-- Integer direction coefficients (05:92–101): for a nonempty `ω ⊆ [d]` there are integers
`a_0, …, a_d` with `a_0 ≠ 0`, `a_0 + ∑_{j∈ω} a_j = 0` and `a_0 + ∑_{j∈ω'} a_j ≠ 0` for `ω' ≠ ω`. -/
theorem direction_integers (d : ℕ) (ω : Finset (Fin d)) (hω : ω.Nonempty) :
    ∃ a : Fin (d + 1) → ℤ, a 0 ≠ 0 ∧ a 0 + ∑ j ∈ ω, a j.succ = 0 ∧
      ∀ ω' : Finset (Fin d), ω' ≠ ω → a 0 + ∑ j ∈ ω', a j.succ ≠ 0 := by
  classical
  let a : Fin (d + 1) → ℤ := Fin.cases (ω.card : ℤ)
    (fun j => if j ∈ ω then -1 else 1)
  refine ⟨a, ?_, ?_, ?_⟩
  · simp only [a, Fin.cases_zero]
    exact_mod_cast (Finset.card_pos.mpr hω).ne'
  · have hωsum : ∑ j ∈ ω, (if j ∈ ω then -1 else 1) =
        -(ω.card : ℤ) := by
      calc
        _ = ∑ _j ∈ ω, (-1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hj]
        _ = -(ω.card : ℤ) := by simp [Finset.sum_const]
    simpa [a, Fin.cases_succ, hωsum]
  · intro ω' hne
    have hsum : ∑ j ∈ ω', a j.succ =
        -((ω' ∩ ω).card : ℤ) + ((ω' \ ω).card : ℤ) := by
      have hdecomp : ω' = ω' ∩ ω ∪ (ω' \ ω) := by
        ext j
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint (ω' ∩ ω) (ω' \ ω) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext j
        simp
      conv_lhs => rw [hdecomp]
      rw [Finset.sum_union hdisj]
      simp only [a, Fin.cases_succ]
      have hleft : ∑ j ∈ ω' ∩ ω, (if j ∈ ω then -1 else 1) =
          -((ω' ∩ ω).card : ℤ) := by
        calc
          _ = ∑ _j ∈ ω' ∩ ω, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_inter] at hj
            simp [hj.2]
          _ = -((ω' ∩ ω).card : ℤ) := by simp [Finset.sum_const]
      have hright : ∑ j ∈ ω' \ ω, (if j ∈ ω then -1 else 1) =
          ((ω' \ ω).card : ℤ) := by
        calc
          _ = ∑ _j ∈ ω' \ ω, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_sdiff] at hj
            simp [hj.2]
          _ = ((ω' \ ω).card : ℤ) := by simp [Finset.sum_const]
      rw [hleft, hright]
    have hcard : (ω.card : ℤ) =
        ((ω \ ω').card : ℤ) + ((ω ∩ ω').card : ℤ) := by
      exact_mod_cast (Finset.card_sdiff_add_card_inter ω ω').symm
    have hneZero : ((ω \ ω').card : ℤ) + ((ω' \ ω).card : ℤ) ≠ 0 := by
      intro hz
      have hleft : ((ω \ ω').card : ℤ) = 0 := by nlinarith
      have hright : ((ω' \ ω).card : ℤ) = 0 := by nlinarith
      have hleftN : (ω \ ω').card = 0 := by exact_mod_cast hleft
      have hrightN : (ω' \ ω).card = 0 := by exact_mod_cast hright
      have hωsub : ω ⊆ ω' := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.card_eq_zero.mp hleftN)
      have hω'sub : ω' ⊆ ω := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.card_eq_zero.mp hrightN)
      exact hne (Finset.Subset.antisymm hω'sub hωsub)
    intro hz
    have hz' : (ω.card : ℤ) +
        ∑ j ∈ ω', a j.succ = 0 := by
      change a 0 + ∑ j ∈ ω', a j.succ = 0
      exact hz
    rw [hsum] at hz'
    rw [Finset.inter_comm ω ω'] at hcard
    apply hneZero
    linarith

/-! ### Parts of `dual_products_orthogonal` (lane opus-dpo split)

The proof of (eq:prediction-dual-products) is assembled below from these part lemmas.  The
nonflat case uses the `PkgB2` state machinery: independent prime replicas in disjoint master
slots, the occurrence rows after inserting translation directions, and the normalized state
average `pkgB2_stateAverage … E N I` after eliminating the directions in `E`.  The shared
definitions `opus_dpo_untranslatedAverage` and `opus_dpo_prefactor` are in `PkgOpusDpo.lean`.

* `opus_dpo_root_mean`: `E_{μ_i}(ν − 1) = o(1)` (the case `b = 0`, 05:162–163).
* `opus_dpo_flat_case`: every type has dimension `0`, so every test is constant in `y`.
* `opus_dpo_replica_identity`: the original pairing is the untranslated replica average.
* `opus_dpo_translation_error`: inserting the averaged translations changes it by `o(1)`
  (05:118–135).
* `opus_dpo_cs_step`: one weighted Cauchy–Schwarz elimination step (05:137–148).
* `opus_dpo_prefactor_bound`: the step prefactor is eventually bounded (linear forms).
* `opus_dpo_terminal`: the final state is `o(1)` (05:159–163). -/

/-- Part: the root mean `E_{μ_i}(ν − 1) → 0` (05:162–163). -/
theorem opus_dpo_root_mean (MS : MasterScales K As sl Dm) (B : Block K) :
    ∀ ε0 > 0, ∀ᶠ N in atTop,
      |Emu MS.core.parameters N B.1 (fun y => nu MS.core.parameters N B y - 1)| ≤ ε0 := by
  intro ε0 hε0
  classical
  let A := MS.core.parameters
  let Tail : ℕ → ℕ → ℝ := fun N σ => parameterTailProductLaw A N B.2.val σ
  let Ref : ℕ → ℕ → ℝ := fun N σ =>
    ∑' y : ℤ, dilationReference
      (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ y * 1
  let V : ℕ → ℕ := fun N => masterScaleV A N B.1
  let Bound : ℕ → ℕ := fun N => ∏ j ∈ B.2.val, (A.X N j) ^ 2
  let Sig : ℕ → Finset ℕ := fun N => Finset.range (Bound N + 1)
  have hNorm (N : ℕ) (j : Fin K) :
      0 < harmonicNormalizer (A.X N j) (primorial (N + 1)) :=
    harmonicNormalizer_pos (A.X N j) (primorial (N + 1)) (primorial_pos _)
      (MS.gapStage.valid_raw_cutoffs N j)
  have hTailZero (N σ : ℕ) (hσ : σ ∉ Sig N) : Tail N σ = 0 := by
    apply parameterTailProductLaw_zero_of_gt A N B.2.val σ
    have hnot : ¬ σ < Bound N + 1 := by
      simpa [Sig, Finset.mem_range] using hσ
    change (∏ j ∈ B.2.val, (A.X N j) ^ 2) < σ
    dsimp [Bound] at hnot ⊢
    omega
  have hTailNonneg (N σ : ℕ) : 0 ≤ Tail N σ := by
    dsimp [Tail]
    exact pkgD_parameterTailProductLaw_nonneg A N B.2.val (fun j => hNorm N j) σ
  have hTailSum (N : ℕ) : ∑ σ ∈ Sig N, Tail N σ = 1 := by
    have htotal := parameterTailProductLaw_tsum_one A N B.2.val
      (fun j => A.Xpos N j) (fun j => hNorm N j)
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simpa [Tail] using hz)] at htotal
    simpa [Tail] using htotal
  have hMuOne (N : ℕ) : Emu A N B.1 (fun _ => 1) = 1 := by
    have hNatSum :
        (∑ n ∈ harmonicNatSupport (A.X N B.1) (primorial (N + 1)),
          harmonicNatLaw (A.X N B.1) (primorial (N + 1)) n) = 1 := by
      have h := harmonicNatLaw_tsum_one (A.X N B.1) (primorial (N + 1))
        (A.Xpos N B.1) (hNorm N B.1)
      rw [tsum_eq_sum
        (s := harmonicNatSupport (A.X N B.1) (primorial (N + 1)))
        (fun n hn => harmonicNatLaw_zero_of_not_mem (A.X N B.1)
          (primorial (N + 1)) n hn)] at h
      exact h
    rw [Emu_eq_harmonicNat_sum]
    simpa using hNatSum
  have hTailCut (N σ : ℕ) (hMass : Tail N σ ≠ 0) :
      0 < σ ∧ Nat.Coprime σ (primorial (N + 1)) ∧ σ ≤ V N := by
    have hprop := parameterTailProductLaw_support_properties A N B.2.val σ (by simpa [Tail] using hMass)
      (fun j => A.Xpos N j)
    refine ⟨hprop.1, hprop.2.1, ?_⟩
    have hprod : (∏ j ∈ B.2.val, (A.X N j) ^ 2) ≤ pkgB2_blockScale A B N := by
      dsimp [pkgB2_blockScale]
      omega
    exact hprop.2.2.trans (hprod.trans (pkgB2_blockScale_le_masterScaleV A B B.1 (fun j hj => B.2.property.2 j hj) N))
  have hRefBound (N : ℕ) (hX2 : 2 ≤ A.X N B.1)
      (hlog : Real.log (A.X N B.1 : ℝ) >
        (primorial (N + 1) : ℝ) / (A.X N B.1 : ℝ))
      (hVX : V N ≤ A.X N B.1) (σ : ℕ) (hMass : Tail N σ ≠ 0) :
      |Ref N σ - 1| ≤ 2 * harmonicDilationUniformError (A.X N B.1)
        (primorial (N + 1)) (V N) := by
    have hcut := hTailCut N σ hMass
    rcases hcut with ⟨hσpos, hcop, hσV⟩
    have hσone : 1 ≤ σ := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hσpos)
    have hσX : σ ≤ A.X N B.1 := hσV.trans hVX
    have hsamp := sampling_pointwise_claim (A.X N B.1) (primorial (N + 1))
      (primorial_pos _) hX2 hlog
    have hD := hsamp.dilation hX2 hlog σ hσone hσX hcop
    have hden : 0 < Real.log (A.X N B.1 : ℝ) -
        (primorial (N + 1) : ℝ) / (A.X N B.1 : ℝ) := by linarith
    have hVone : 1 ≤ V N := by
      dsimp [V, masterScaleV]
      omega
    have hres := harmonicResidueError_le_two_dilation
      (A.X N B.1) (primorial (N + 1)) σ (V N) (A.Xpos N B.1)
      hVone hσV hden
    have hRefErr : |Ref N σ - 1| ≤
        harmonicResidueError (A.X N B.1) (primorial (N + 1)) σ := by
      simpa [Ref] using hD.2
    exact hRefErr.trans hres
  have hNuPair (N : ℕ) :
      Emu A N B.1 (fun y => nu A N B y) =
        ∑' σ : ℕ, Tail N σ * Ref N σ := by
    have h := nuWeightedPairing_eq A N B (fun _ : ℤ => (1 : ℝ))
    simpa [Tail, Ref] using h
  have hOuter (N : ℕ) :
      (∑' σ : ℕ, Tail N σ * Ref N σ) =
        ∑ σ ∈ Sig N, Tail N σ * Ref N σ := by
    rw [tsum_eq_sum (s := Sig N) (fun σ hσ => by
      have hz := hTailZero N σ hσ
      simp [Tail, hz])]
  have hEsub (N : ℕ) :
      Emu A N B.1 (fun y => nu A N B y - 1) =
        Emu A N B.1 (fun y => nu A N B y) - 1 := by
    have hsub := pkgD_Emu_add A N B.1 (fun y => nu A N B y - 1) (fun _ => 1)
    have heq : (fun y => (nu A N B y - 1) + 1) = fun y => nu A N B y := by
      funext y; ring
    rw [heq] at hsub
    rw [hMuOne N] at hsub
    linarith
  have hError : ∀ᶠ N in atTop,
      2 * harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N) ≤ ε0 := by
    have h := (pivotDilationError_tendsto A B.1).1
    have hmul : Tendsto (fun N => 2 * harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N))
        atTop (𝓝 (2 * 0)) := h.const_mul 2
    rw [mul_zero] at hmul
    filter_upwards [hmul.eventually_lt_const hε0] with N hN
    exact hN.le
  have hVle : ∀ᶠ N in atTop, V N ≤ A.X N B.1 := (pivotDilationError_tendsto A B.1).2
  filter_upwards [pivotSamplingEventually MS B.1, hVle, hError] with N ⟨hX2, hlog⟩ hVX hErr
  rw [hEsub N, hNuPair N, hOuter N]
  have hDiff : (∑ σ ∈ Sig N, Tail N σ * Ref N σ) - 1 =
      ∑ σ ∈ Sig N, Tail N σ * (Ref N σ - 1) := by
    conv_lhs => rw [← hTailSum N]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring


  rw [hDiff]
  calc
    |∑ σ ∈ Sig N, Tail N σ * (Ref N σ - 1)| ≤
        ∑ σ ∈ Sig N, |Tail N σ * (Ref N σ - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ ∈ Sig N, Tail N σ * |Ref N σ - 1| := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [abs_mul, abs_of_nonneg (hTailNonneg N σ)]
    _ ≤ ∑ σ ∈ Sig N, Tail N σ * (2 * harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N)) := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hz : Tail N σ = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hRefBound N hX2 hlog hVX σ hz) (hTailNonneg N σ)
    _ = (∑ σ ∈ Sig N, Tail N σ) * (2 * harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N)) := by
      rw [Finset.sum_mul]
    _ = 2 * harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) (V N) := by
      rw [hTailSum N, one_mul]
    _ ≤ ε0 := hErr


/-- Part: flat types.  If every type has dimension `0`, every dual test is independent of `y` and
bounded by `1` in absolute value, so the claim reduces to `opus_dpo_root_mean`.  (This covers
`b = 0`.) -/
theorem opus_dpo_flat_case (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (hflat : ∀ k, (T k).d = 0) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε := by
  intro ε hε
  have hroot := opus_dpo_root_mean MS B ε hε
  filter_upwards [hroot] with N hroot
  intro I
  let c : ℝ := ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) 0
  have hfactor (k : Fin b) :
      |dualTest MS B (T k) (gap k) (J0 k) N (I k) 0| ≤ 1 :=
    l_dflat_dualTest_abs_le_one MS B (T k) (gap k) (J0 k) N (I k) (hflat k) 0
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro k hk
      exact abs_nonneg _
    · intro k hk
      exact hfactor k
  have hproduct (y : ℤ) :
      (∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) = c := by
    dsimp [c]
    apply Finset.prod_congr rfl
    intro k hk
    rw [l_dflat_dualTest_eq_goodSlotAverage MS B (T k) (gap k) (J0 k) N (I k)
      (hflat k) y]
    rw [l_dflat_dualTest_eq_goodSlotAverage MS B (T k) (gap k) (J0 k) N (I k)
      (hflat k) 0]
  have hfun :
      (fun y : ℤ => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) =
      (fun y => c * (nu MS.core.parameters N B y - 1)) := by
    funext y
    rw [hproduct y]
    ring
  calc
    |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| =
      |c * Emu MS.core.parameters N B.1 (fun y => nu MS.core.parameters N B y - 1)| := by
        rw [hfun, Emu_mul_left]
    _ = |c| * |Emu MS.core.parameters N B.1
        (fun y => nu MS.core.parameters N B y - 1)| := abs_mul _ _
    _ ≤ 1 * |Emu MS.core.parameters N B.1
        (fun y => nu MS.core.parameters N B y - 1)| :=
          mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ ε := by simpa using hroot

/-- Part: replica expansion (05:87–90).  Eventually, for all inputs, the original pairing equals
the untranslated replica average: independent primes for each test in disjoint master-slot
blocks (unused slots integrate to one; the joint good probability is the product of the
per-test good probabilities), the pivot `y ∼ μ_i` and the original shifts as signed uniform
interval coordinates, every translation coordinate set to zero. -/
theorem opus_dpo_replica_identity (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ) :
    ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y) =
      opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I := by
  sorry

/-- Part: translation insertion (05:118–135).  Inserting the averaged translations along the
fixed directions changes the untranslated average by `o(1)`, uniformly over the inputs: the
integrand is bounded by `(1 + V_B)^{1 + #rows}`, while the harmonic and interval translation
errors are super-polynomially small in `V_B`. -/
theorem opus_dpo_translation_error (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I -
        pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 ∅ N I| ≤ ε := by
  exact opus_dpo_translation_error_proof MS B gap T J0 hgap hT hJ0 direction hdir k0

/-- Part: one weighted Cauchy–Schwarz elimination step (05:137–148).  Eliminating the direction
of the nonroot row `s ∉ E`: the copies of row `s` do not depend on its translation coordinate,
they are bounded by their `(1 + ν)` weights `Ω`, and squaring duplicates that coordinate. -/
theorem opus_dpo_cs_step (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (hs : s ∉ E) :
    ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 E N I| ^ 2 ≤
        opus_dpo_prefactor MS B gap T J0 hT direction E s N *
          pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (insert s E) N I := by
  sorry

/-- Part: the elimination prefactor is eventually nonnegative and bounded (expand `Ω` into
`ν`-monomials over the copies of row `s` and apply the weighted linear-forms estimate,
`pkgB2_weightedGoodMonomial_tendsto_one`; the limit is `2^{#copies}`). -/
theorem opus_dpo_prefactor_bound (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (hs : s ∉ E) :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      0 ≤ opus_dpo_prefactor MS B gap T J0 hT direction E s N ∧
        opus_dpo_prefactor MS B gap T J0 hT direction E s N ≤ C := by
  classical
  let L : ℝ := (2 : ℝ) ^ (Finset.univ.filter
    (fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
      (pkgB2_occurrenceEnum T E o).1 = Sum.inr s)).card
  have hlim := l_dpre_prefactor_tendsto MS B gap T J0 hgap hT hJ0
    direction hdir k0 E s
  have hclose : ∀ᶠ N : ℕ in atTop,
      dist (opus_dpo_prefactor MS B gap T J0 hT direction E s N) L < 1 := by
    have h := hlim.eventually
      (Metric.ball_mem_nhds L (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h] with N hN
    simpa only [Metric.mem_ball] using hN
  refine ⟨L + 1, ?_⟩
  filter_upwards [hclose] with N hN
  refine ⟨l_dpre_prefactor_nonneg MS B gap T J0 hT direction E s N, ?_⟩
  have habs :
      |opus_dpo_prefactor MS B gap T J0 hT direction E s N - L| < 1 := by
    simpa [Real.dist_eq] using hN
  have := abs_lt.mp habs
  dsimp [L]
  linarith

/-- Part: the terminal state, with every direction eliminated, is `o(1)` uniformly over the
inputs (05:159–163; `pkgB2_terminalState_tendsto_zero` for input sequences, here uniform and
without `0 < sl`). -/
theorem opus_dpo_terminal (MS : MasterScales K As sl Dm) (B : Block K) {b : ℕ}
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (hNonroot : Nonempty (pkgB2_Nonroot T)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 Finset.univ N I| ≤ ε := by
  sorry

/-- (eq:prediction-dual-products), 05:68–74 and 129–164: for every fixed `b` and fixed tests at
the same block (possibly different valid gaps, allowed types and `J₀`),
`E_{μ_i}(ν − 1) ∏_{k<b} 𝒟_k = o(1)` uniformly over their inputs. -/
theorem dual_products_orthogonal (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε := by
  classical
  by_cases hflat : ∀ k, (T k).d = 0
  · exact opus_dpo_flat_case MS B gap T J0 hgap hT hJ0 hflat
  push_neg at hflat
  obtain ⟨k0, hk0⟩ := hflat
  have hNonroot : Nonempty (pkgB2_Nonroot T) :=
    ⟨⟨k0, ⟨Finset.univ, Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hk0⟩⟩⟩⟩⟩
  -- Fixed direction integers for every nonroot row (05:92–101).
  let direction : ∀ s : pkgB2_Nonroot T, Fin ((T s.1).d + 1) → ℤ := fun s =>
    Classical.choose (direction_integers (T s.1).d s.2.1 s.2.2)
  have hdir : pkgB2_directionSpec T direction := fun s =>
    Classical.choose_spec (direction_integers (T s.1).d s.2.1 s.2.2)
  -- Eliminate the directions in a fixed order: `Ej j` holds the first `j` of them.
  let n := Fintype.card (pkgB2_Nonroot T)
  let e : Fin n ≃ pkgB2_Nonroot T := (Fintype.equivFin _).symm
  let Ej : ℕ → Finset (pkgB2_Nonroot T) := fun j =>
    (Finset.univ.filter fun i : Fin n => i.val < j).image e
  let a : ℕ → (N : ℕ) → ((k : Fin b) → DualInput MS B (T k) N) → ℝ := fun j N I =>
    pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (Ej j) N I
  have hEsucc (j : ℕ) (hj : j < n) : Ej (j + 1) = insert (e ⟨j, hj⟩) (Ej j) := by
    ext t
    simp only [Ej, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hij : i.val = j
      · left
        congr 1
        exact Fin.ext hij
      · right
        exact ⟨i, by omega, rfl⟩
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨⟨j, hj⟩, by simp, rfl⟩
      · exact ⟨i, by omega, rfl⟩
  have hEnot (j : ℕ) (hj : j < n) : e ⟨j, hj⟩ ∉ Ej j := by
    intro hmem
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
    have hij := e.injective heq
    have hlt := (Finset.mem_filter.mp hi).2
    rw [hij] at hlt
    exact lt_irrefl _ hlt
  have hE0 : Ej 0 = ∅ := by
    simp [Ej]
  have hEn : Ej n = Finset.univ := by
    ext t
    simp only [Ej, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨e.symm t, (e.symm t).isLt, e.apply_symm_apply t⟩
  -- One Cauchy–Schwarz step per direction, with an input-free bounded prefactor.
  have hstep : ∀ j < n, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ∀ I : (k : Fin b) → DualInput MS B (T k) N, |a j N I| ^ 2 ≤ C * |a (j + 1) N I| := by
    intro j hj
    obtain ⟨C, hC⟩ := opus_dpo_prefactor_bound MS B gap T J0 hgap hT hJ0 direction hdir k0
      (Ej j) (e ⟨j, hj⟩) (hEnot j hj)
    have hcs := opus_dpo_cs_step MS B gap T J0 hgap hT hJ0 direction hdir k0
      (Ej j) (e ⟨j, hj⟩) (hEnot j hj)
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    filter_upwards [hC, hcs] with N hCN hcsN I
    have h1 := hcsN I
    rw [← hEsucc j hj] at h1
    obtain ⟨hP0, hPC⟩ := hCN
    calc |a j N I| ^ 2 ≤ opus_dpo_prefactor MS B gap T J0 hT direction (Ej j) (e ⟨j, hj⟩) N *
          a (j + 1) N I := h1
      _ ≤ opus_dpo_prefactor MS B gap T J0 hT direction (Ej j) (e ⟨j, hj⟩) N *
          |a (j + 1) N I| := mul_le_mul_of_nonneg_left (le_abs_self _) hP0
      _ ≤ max C 0 * |a (j + 1) N I| :=
          mul_le_mul_of_nonneg_right (hPC.trans (le_max_left _ _)) (abs_nonneg _)
  have hlast : ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |a n N I| ≤ ε := by
    intro ε hε
    filter_upwards [opus_dpo_terminal MS B gap T J0 hgap hT hJ0 direction hdir k0 hNonroot
      ε hε] with N hN I
    show |pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (Ej n) N I| ≤ ε
    rw [hEn]
    exact hN I
  have hzero := opus_dpo_iterate (X := fun N => (k : Fin b) → DualInput MS B (T k) N)
    n a hstep hlast
  -- Replica expansion, translation insertion, and the iterated elimination.
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [opus_dpo_replica_identity MS B gap T J0 hgap hT hJ0 direction,
    opus_dpo_translation_error MS B gap T J0 hgap hT hJ0 direction hdir k0 (ε / 2) hε2,
    hzero (ε / 2) hε2] with N hid htr hz I
  rw [hid I]
  have h0 : a 0 N I =
      pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 ∅ N I := by
    show pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 (Ej 0) N I = _
    rw [hE0]
  have hz' := hz I
  rw [h0] at hz'
  have htr' := htr I
  calc _ = |(opus_dpo_untranslatedAverage MS B gap T J0 hT direction N I -
          pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 ∅ N I) +
          pkgB2_stateAverage MS B gap T J0 hgap hT hJ0 direction hdir k0 ∅ N I| := by
        rw [sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add htr' hz'
    _ = ε := by ring

/-- (eq:prediction-dual-moments), 05:74–79 and 166–175: for every fixed `b ≥ 1` and a type of
dimension `≤ d_*`, `E_{μ_i}(1 + ν)|𝒟|^b ≤ 2 A_*^b + o(1)` uniformly over the inputs. -/
theorem dual_moment_bound (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (b : ℕ) (hb : 0 < b) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε := by
  intro ε hε
  have htwoExp : (1 + b * (2 ^ T.d - 1)) ≤
      1 + b * (2 ^ dStar - 1) := by
    have hpow : 2 ^ T.d ≤ 2 ^ dStar := Nat.pow_le_pow_right (by omega) hd
    have hsub : 2 ^ T.d - 1 ≤ 2 ^ dStar - 1 := Nat.sub_le_sub_right hpow 1
    exact Nat.add_le_add_left (Nat.mul_le_mul_left b hsub) 1
  have hcount : (2 : ℝ) ^ (1 + b * (2 ^ T.d - 1)) ≤
      2 * dualMomentConstant dStar ^ b := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) htwoExp
    have hconst : 2 * dualMomentConstant dStar ^ b =
        (2 : ℝ) ^ (1 + b * (2 ^ dStar - 1)) := by
      unfold dualMomentConstant
      calc
        _ = (2 : ℝ) ^ 1 * ((2 : ℝ) ^ (2 ^ dStar - 1)) ^ b := by norm_num
        _ = (2 : ℝ) ^ (1 + (2 ^ dStar - 1) * b) := by
          rw [← pow_mul, ← pow_add]
        _ = _ := by congr 1; rw [Nat.mul_comm]
    exact hpow.trans (le_of_eq hconst.symm)
  have hMoment := pkgB_dualMoment_bound_asymptotic
    MS B l hgap T hT J0 hJ0 b hb ε hε
  filter_upwards [hMoment] with N hN
  intro I
  have hI := hN I
  have hI' : Emu MS.core.parameters N B.1
      (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y| ^ b) ≤
      (2 : ℝ) ^ (1 + b * (2 ^ T.d - 1)) + ε := hI
  linarith [hI', hcount]

/-- Clipping, 05:80–82 and 177–184: for fixed `K > A_*` and fixed `p ≥ 1`,
`E_{μ_i}(1 + ν)|𝒟 − 𝒟^{[K]}|^p = o(1)` uniformly over the inputs. -/
theorem dual_clipping_error (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) (hgap : ValidGap B l) (hT : Allowed Dm T) (hJ0 : 0 < J0)
    (dStar : ℕ) (hd : T.d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc)
    (p : ℕ) (hp : 0 < p) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
      Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
        |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε := by
  intro ε hε
  let Astar : ℝ := dualMomentConstant dStar
  have hApos : 0 < Astar := by
    dsimp [Astar, dualMomentConstant]
    positivity
  have hAone : 1 ≤ Astar := by
    dsimp [Astar, dualMomentConstant]
    exact one_le_pow₀ (by norm_num)
  have hKpos : 0 < Kc := lt_trans hApos hK
  have hKone : 1 < Kc := lt_of_le_of_lt hAone hK
  let ratioA : ℝ := Astar / Kc
  let ratioK : ℝ := 1 / Kc
  have hratioA0 : 0 ≤ ratioA := by positivity
  have hratioA1 : ratioA < 1 := (div_lt_one hKpos).2 hK
  have hratioK0 : 0 ≤ ratioK := by positivity
  have hratioK1 : ratioK < 1 := (div_lt_one hKpos).2 hKone
  have hpowA : Tendsto (fun n : ℕ => ratioA ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratioA0 hratioA1
  have hpowK : Tendsto (fun n : ℕ => ratioK ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratioK0 hratioK1
  have hsmall : Tendsto
      (fun n : ℕ => 2 * Astar ^ p * ratioA ^ n + ratioK ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpowA).add hpowK
  let Cseq : ℕ → ℝ := fun n =>
    Kc ^ p * (Kc ^ (p + n))⁻¹ * (2 * Astar ^ (p + n) + 1)
  have hCeq (n : ℕ) :
      Cseq n = 2 * Astar ^ p * ratioA ^ n + ratioK ^ n := by
    dsimp [Cseq, ratioA, ratioK]
    rw [pow_add, pow_add]
    have hcancel : Kc ^ p * (Kc ^ p * Kc ^ n)⁻¹ = (Kc ^ n)⁻¹ := by
      field_simp [ne_of_gt (pow_pos hKpos p), ne_of_gt (pow_pos hKpos n)]
    calc
      Kc ^ p * (Kc ^ p * Kc ^ n)⁻¹ * (2 * (Astar ^ p * Astar ^ n) + 1) =
          (Kc ^ n)⁻¹ * (2 * (Astar ^ p * Astar ^ n) + 1) := by rw [hcancel]
      _ = 2 * Astar ^ p * (Astar ^ n / Kc ^ n) + 1 / Kc ^ n := by
        field_simp [ne_of_gt (pow_pos hKpos n)]
      _ = 2 * Astar ^ p * (Astar / Kc) ^ n + (1 / Kc) ^ n := by
        have h1 : (1 / Kc) ^ n = 1 / Kc ^ n := by
          simpa using (div_pow (1 : ℝ) Kc n)
        calc
          _ = 2 * Astar ^ p * (Astar / Kc) ^ n + 1 / Kc ^ n := by
            rw [← div_pow]
          _ = 2 * Astar ^ p * (Astar / Kc) ^ n + (1 / Kc) ^ n := by
            rw [← h1]
  have hCseq : Tendsto Cseq atTop (𝓝 0) := by
    apply hsmall.congr'
    filter_upwards with n
    exact (hCeq n).symm
  have hevent : ∀ᶠ n : ℕ in atTop, Cseq n < ε :=
    hCseq.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hevent
  have hCsmall : Cseq n < ε := hn n le_rfl
  let b : ℕ := p + n
  have hpb : p ≤ b := by dsimp [b]; omega
  have hb : 0 < b := lt_of_lt_of_le hp hpb
  let Ctail : ℝ := Kc ^ p * (Kc ^ b)⁻¹
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hmoment :=
    dual_moment_bound MS B l T J0 hgap hT hJ0 dStar hd b hb 1 (by norm_num)
  filter_upwards [hmoment] with N hmomentN
  intro I
  let D : ℤ → ℝ := dualTest MS B T l J0 N I
  let w : ℤ → ℝ := fun y => 1 + nu MS.core.parameters N B y
  have hw (y : ℤ) : 0 ≤ w y := by
    have h := I.g_bound (∅ : Finset (Fin T.d)) (fun _ => 0) y
    exact le_trans (abs_nonneg _) h
  have hpoint (y : ℤ) :
      w y * |D y - clip Kc (D y)| ^ p ≤ Ctail * (w y * |D y| ^ b) := by
    have hclip := clip_error_pow_le Kc (D y) hKpos p b hpb hp
    calc
      w y * |D y - clip Kc (D y)| ^ p ≤
          w y * (Ctail * |D y| ^ b) :=
        mul_le_mul_of_nonneg_left hclip (hw y)
      _ = Ctail * (w y * |D y| ^ b) := by ring
  have hresult :
      Emu MS.core.parameters N B.1 (fun y => w y * |D y - clip Kc (D y)| ^ p) < ε := by
   calc
    Emu MS.core.parameters N B.1 (fun y => w y * |D y - clip Kc (D y)| ^ p)
        ≤ Emu MS.core.parameters N B.1 (fun y => Ctail * (w y * |D y| ^ b)) :=
      pkgB_Emu_mono MS.core.parameters N B.1 hpoint
    _ = Ctail * Emu MS.core.parameters N B.1 (fun y => w y * |D y| ^ b) :=
      Emu_mul_left MS.core.parameters N B.1 Ctail (fun y => w y * |D y| ^ b)
    _ ≤ Ctail * (2 * Astar ^ b + 1) :=
      mul_le_mul_of_nonneg_left (hmomentN I) hCtail
    _ < ε := by
      have heq : Ctail * (2 * Astar ^ b + 1) = Cseq n := by
        dsimp [Ctail, Cseq, b]
      rw [heq]
      exact hCsmall
  exact le_of_lt (by simpa [w, D] using hresult)

/-- 05:80–82 and 184–189: (eq:prediction-dual-products) remains true for clipped tests, for a
common clipping bound `K > A_*`. -/
theorem dual_products_orthogonal_clipped (MS : MasterScales K As sl Dm) (B : Block K) (b : ℕ)
    (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k)) (hJ0 : ∀ k, 0 < J0 k)
    (dStar : ℕ) (hd : ∀ k, (T k).d ≤ dStar) (Kc : ℝ) (hK : dualMomentConstant dStar < Kc) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
      |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
        ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε := by
  intro ε hε
  by_cases hb0 : b = 0
  · subst b
    simpa using
      (dual_products_orthogonal MS B 0 gap T J0 hgap hT hJ0 ε hε)
  · have hb : 0 < b := Nat.pos_of_ne_zero hb0
    let Astar : ℝ := dualMomentConstant dStar
    have hApos : 0 < Astar := by
      dsimp [Astar, dualMomentConstant]
      positivity
    let M : ℝ := 2 * Astar ^ b + 1
    have hMone : 1 ≤ M := by
      dsimp [M]
      nlinarith [pow_nonneg (le_of_lt hApos) b]
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMone
    let theta : ℝ := ε / (4 * (b : ℝ))
    have htheta : 0 < theta := by dsimp [theta]; positivity
    let rtail : ℝ := theta / M ^ b
    have hrtail : 0 < rtail := by dsimp [rtail]; positivity
    let delta : ℝ := rtail ^ b
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    let pRoot : ℝ := 1 / (b : ℝ)
    have hbReal : 0 < (b : ℝ) := by exact_mod_cast hb
    have hpNat : (b : ℝ) * pRoot = 1 := by
      dsimp [pRoot]
      exact mul_one_div_cancel hbReal.ne'
    have hdeltaRoot : delta ^ pRoot = rtail := by
      dsimp [delta, pRoot]
      rw [← Real.rpow_natCast_mul (le_of_lt hrtail), hpNat, Real.rpow_one]
    have horth :=
      dual_products_orthogonal MS B b gap T J0 hgap hT hJ0 (ε / 2) (by positivity)
    have hmomentEach (k : Fin b) :
        ∀ᶠ N in atTop, ∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y| ^ b) ≤ M := by
      have hm := dual_moment_bound MS B (gap k) (T k) (J0 k)
        (hgap k) (hT k) (hJ0 k) dStar (hd k) b hb 1 (by norm_num)
      simpa [M, Astar] using hm
    have hclipEach (k : Fin b) :
        ∀ᶠ N in atTop, ∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y -
                clip Kc (dualTest MS B (T k) (gap k) (J0 k) N Ik y)| ^ b) ≤ delta :=
      dual_clipping_error MS B (gap k) (T k) (J0 k)
        (hgap k) (hT k) (hJ0 k) dStar (hd k) Kc hK b hb delta hdelta
    have hAll : ∀ᶠ N in atTop, ∀ k : Fin b,
        (∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y| ^ b) ≤ M) ∧
        (∀ Ik : DualInput MS B (T k) N,
          Emu MS.core.parameters N B.1
            (fun y => (1 + nu MS.core.parameters N B y) *
              |dualTest MS B (T k) (gap k) (J0 k) N Ik y -
                clip Kc (dualTest MS B (T k) (gap k) (J0 k) N Ik y)| ^ b) ≤ delta) := by
      have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
        (fun k _ => (hmomentEach k).and (hclipEach k))
      simpa using h
    filter_upwards [horth, hAll] with N horthN hAllN
    intro I
    let D : Fin b → ℤ → ℝ := fun k y =>
      dualTest MS B (T k) (gap k) (J0 k) N (I k) y
    let C : Fin b → ℤ → ℝ := fun k y => clip Kc (D k y)
    let w : ℤ → ℝ := fun y => 1 + nu MS.core.parameters N B y
    have hw (y : ℤ) : 0 ≤ w y := by
      dsimp [w]
      exact add_nonneg (by norm_num) (pkgB_nu_nonneg MS.core.parameters N B y)
    have hrootAbs (y : ℤ) :
        |nu MS.core.parameters N B y - 1| ≤ w y := by
      dsimp [w]
      exact abs_sub_one_le_add_one (pkgB_nu_nonneg MS.core.parameters N B y)
    let term : Fin b → ℤ → ℝ := fun i y =>
      |C i y - D i y| *
        ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|)
    let F : Fin b → Fin b → ℤ → ℝ := fun i k y =>
      if k = i then D i y - C i y else D k y
    have hFprod (i : Fin b) (y : ℤ) :
        ∏ k : Fin b, |F i k y| = term i y := by
      dsimp [F, term]
      calc
        ∏ k : Fin b, |if k = i then D i y - C i y else D k y| =
            ∏ k : Fin b, if k = i then |D i y - C i y| else |D k y| := by
              apply Finset.prod_congr rfl
              intro k hk
              by_cases hki : k = i <;> simp [hki]
        _ = |D i y - C i y| *
            ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|) :=
          prod_ite_factorization (Finset.univ : Finset (Fin b)) i
            (Finset.mem_univ i) _ _
        _ = |C i y - D i y| *
            ∏ k : Fin b, (if k = i then (1 : ℝ) else |D k y|) := by
              rw [abs_sub_comm]
    have htel (y : ℤ) :
        |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y| ≤
          ∑ k : Fin b, term k y := by
      have hbase := abs_prod_sub_prod_le (Finset.univ : Finset (Fin b))
        (fun k => C k y) (fun k => D k y)
      have hmax (k : Fin b) :
          max (|C k y|) (|D k y|) = |D k y| :=
        max_eq_right (clip_abs_le_abs Kc (D k y) (le_of_lt (lt_trans hApos hK)))
      simpa [term, hmax] using hbase
    letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    have hholder (i : Fin b) :
        Emu MS.core.parameters N B.1 (fun y => w y * term i y) ≤
          ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot := by
      calc
        Emu MS.core.parameters N B.1 (fun y => w y * term i y) =
            Emu MS.core.parameters N B.1
              (fun y => w y * ∏ k : Fin b, |F i k y|) := by
                congr 1
                funext y
                rw [hFprod i y]
        _ ≤ ∏ k : Fin b,
              (Emu MS.core.parameters N B.1
                (fun y => w y * |F i k y| ^ (Finset.univ : Finset (Fin b)).card)) ^
                  (1 / ((Finset.univ : Finset (Fin b)).card : ℝ)) :=
          Emu_weighted_holder (Finset.univ : Finset (Fin b)) Finset.univ_nonempty
            MS.core.parameters N B.1 w (F i) hw
        _ = _ := by simp [Finset.card_fin, pRoot]
    have hmomentNonneg (i k : Fin b) :
        0 ≤ Emu MS.core.parameters N B.1
          (fun y => w y * |F i k y| ^ b) :=
      pkgB_Emu_nonneg MS.core.parameters N B.1
        (fun y => mul_nonneg (hw y) (pow_nonneg (abs_nonneg _) _))
    have hmomentRootBound (i k : Fin b) :
        (Emu MS.core.parameters N B.1
          (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤
            if k = i then rtail else M := by
      by_cases hki : k = i
      · subst k
        have herr := (hAllN i).2 (I i)
        have hbound : Emu MS.core.parameters N B.1
            (fun y => w y * |F i i y| ^ b) ≤ delta := by
          simpa [F, D, C, w] using herr
        have hroot : (Emu MS.core.parameters N B.1
            (fun y => w y * |F i i y| ^ b)) ^ pRoot ≤ rtail := by
          calc
            _ ≤ delta ^ pRoot :=
              Real.rpow_le_rpow (hmomentNonneg i i) hbound (by positivity)
            _ = rtail := hdeltaRoot
        simpa using hroot
      · have hbound : Emu MS.core.parameters N B.1
            (fun y => w y * |F i k y| ^ b) ≤ M := by
          simpa [F, hki, D, w] using (hAllN k).1 (I k)
        have hp_le_one : pRoot ≤ 1 := by
          have hbcast : 1 ≤ (b : ℝ) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb))
          dsimp [pRoot]
          calc
            1 / (b : ℝ) ≤ 1 / 1 :=
              one_div_le_one_div_of_le (by norm_num) hbcast
            _ = 1 := by norm_num
        have hroot : (Emu MS.core.parameters N B.1
            (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤ M := by
          calc
          _ ≤ M ^ pRoot :=
            Real.rpow_le_rpow (hmomentNonneg i k) hbound (by positivity)
          _ ≤ M := by
            simpa using Real.rpow_le_rpow_of_exponent_le hMone hp_le_one
        simpa [hki] using hroot
    have hrootProd (i : Fin b) :
        ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤ theta := by
      have hprod :
          ∏ k : Fin b,
            (Emu MS.core.parameters N B.1
              (fun y => w y * |F i k y| ^ b)) ^ pRoot ≤
            ∏ k : Fin b, (if k = i then rtail else M) :=
        Finset.prod_le_prod₀
          (fun k _ => Real.rpow_nonneg (hmomentNonneg i k) _)
          (fun k _ => hmomentRootBound i k)
      have hrest :
          ∏ k ∈ (Finset.univ : Finset (Fin b)),
              (if k = i then (1 : ℝ) else M) ≤ M ^ b := by
        calc
          ∏ k ∈ (Finset.univ : Finset (Fin b)), (if k = i then (1 : ℝ) else M) ≤
              ∏ k ∈ (Finset.univ : Finset (Fin b)), M :=
            Finset.prod_le_prod₀
              (fun k _ => by
                by_cases hk : k = i
                · simp [hk]
                · simp [hk, hMpos.le])
              (fun k _ => by
                by_cases hk : k = i
                · simpa [hk] using hMone
                · simp [hk])
          _ = M ^ b := by simp
      calc
        _ ≤ ∏ k : Fin b, (if k = i then rtail else M) := hprod
        _ = rtail * ∏ k : Fin b, (if k = i then (1 : ℝ) else M) :=
          prod_ite_factorization (Finset.univ : Finset (Fin b)) i
            (Finset.mem_univ i) rtail (fun _ => M)
        _ ≤ rtail * M ^ b :=
          mul_le_mul_of_nonneg_left hrest (le_of_lt hrtail)
        _ = theta := by
          dsimp [rtail]
          field_simp [ne_of_gt (pow_pos hMpos b)]
    have htermBound (i : Fin b) : Emu MS.core.parameters N B.1
        (fun y => w y * term i y) ≤ theta :=
      (hholder i).trans (hrootProd i)
    have hdiffBound :
        Emu MS.core.parameters N B.1
          (fun y => w y *
            |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y|) ≤
          (b : ℝ) * theta := by
      calc
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => w y * ∑ k : Fin b, term k y) :=
          pkgB_Emu_mono MS.core.parameters N B.1 (fun y =>
            mul_le_mul_of_nonneg_left (htel y) (hw y))
        _ = ∑ k : Fin b, Emu MS.core.parameters N B.1
              (fun y => w y * term k y) := by
          simpa [Finset.mul_sum] using
            Emu_finset_sum MS.core.parameters N B.1
              (Finset.univ : Finset (Fin b)) (fun k y => w y * term k y)
        _ ≤ ∑ _k : Fin b, theta := Finset.sum_le_sum fun k _ => htermBound k
        _ = (b : ℝ) * theta := by simp [Finset.sum_const, Finset.card_fin]
    have hdiffAbs :
        |Emu MS.core.parameters N B.1
          (fun y => (nu MS.core.parameters N B y - 1) *
            ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y))| ≤
          (b : ℝ) * theta := by
      calc
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => |(nu MS.core.parameters N B y - 1) *
              ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)|) :=
          pkgB_Emu_abs_le MS.core.parameters N B.1 _
        _ ≤ Emu MS.core.parameters N B.1
            (fun y => w y *
              |(∏ k : Fin b, C k y) - ∏ k : Fin b, D k y|) :=
          pkgB_Emu_mono MS.core.parameters N B.1 (fun y => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hrootAbs y) (abs_nonneg _))
        _ ≤ (b : ℝ) * theta := hdiffBound
    have hlinear :
        Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, C k y) =
          Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y) +
          Emu MS.core.parameters N B.1
            (fun y => (nu MS.core.parameters N B y - 1) *
              ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)) := by
      calc
        _ = Emu MS.core.parameters N B.1
              (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y +
                (nu MS.core.parameters N B y - 1) *
                  ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y)) := by
            congr 1
            funext y
            ring
        _ = _ := pkgB_Emu_add MS.core.parameters N B.1 _ _
    calc
      |Emu MS.core.parameters N B.1
          (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, C k y)|
          ≤ (ε / 2) + (b : ℝ) * theta := by
              rw [hlinear]
              calc
                _ ≤
                    |Emu MS.core.parameters N B.1
                      (fun y => (nu MS.core.parameters N B y - 1) * ∏ k : Fin b, D k y)| +
                    |Emu MS.core.parameters N B.1
                      (fun y => (nu MS.core.parameters N B y - 1) *
                        ((∏ k : Fin b, C k y) - ∏ k : Fin b, D k y))| :=
                  abs_add_le _ _
                _ ≤ (ε / 2) + (b : ℝ) * theta :=
                  add_le_add (by simpa [D] using horthN I) hdiffAbs
      _ ≤ ε := by
        dsimp [theta]
        have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
        have hbRne : (b : ℝ) ≠ 0 := ne_of_gt hbR
        field_simp [hbRne]
        linarith

/-- Lemma `lem:dual-pseudorandomness` (05:68–83), assembled from its three parts. -/
theorem dual_pseudorandomness (MS : MasterScales K As sl Dm) (B : Block K) (dStar : ℕ) :
    (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
      (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
        |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
          ∏ k, dualTest MS B (T k) (gap k) (J0 k) N (I k) y)| ≤ ε) ∧
    (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
      T.d ≤ dStar → ∀ b : ℕ, 0 < b →
      ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          |dualTest MS B T l J0 N I y| ^ b) ≤ 2 * dualMomentConstant dStar ^ b + ε) ∧
    (∀ Kc : ℝ, dualMomentConstant dStar < Kc →
      (∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ), ValidGap B l → Allowed Dm T → 0 < J0 →
        T.d ≤ dStar → ∀ p : ℕ, 0 < p →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
            |dualTest MS B T l J0 N I y - clip Kc (dualTest MS B T l J0 N I y)| ^ p) ≤ ε) ∧
      (∀ (b : ℕ) (gap : Fin b → Fin K) (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ),
        (∀ k, ValidGap B (gap k)) → (∀ k, Allowed Dm (T k)) → (∀ k, 0 < J0 k) →
        (∀ k, (T k).d ≤ dStar) →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : (k : Fin b) → DualInput MS B (T k) N,
          |Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (T k) (gap k) (J0 k) N (I k) y))| ≤ ε)) := by
  refine ⟨fun b gap T J0 hgap hT hJ0 => dual_products_orthogonal MS B b gap T J0 hgap hT hJ0,
    fun l T J0 hgap hT hJ0 hd b hb => dual_moment_bound MS B l T J0 hgap hT hJ0 dStar hd b hb,
    fun Kc hK => ⟨fun l T J0 hgap hT hJ0 hd p hp =>
      dual_clipping_error MS B l T J0 hgap hT hJ0 dStar hd Kc hK p hp,
      fun b gap T J0 hgap hT hJ0 hd =>
        dual_products_orthogonal_clipped MS B b gap T J0 hgap hT hJ0 dStar hd Kc hK⟩⟩

/-! ### Proposition `prop:dense-model` (05:199–248) -/

/-- The bounded dense-model property (eq:prediction-dense-approximation): `F` is `[0,1]`-valued
and, for every master block, scale label `a ∈ 𝒜`, colour, valid gap, allowed cube type (any
dimension) and fixed `J₀`, `E_{μ_i}(ρ − F)𝒟 = o(1)` uniformly over the inputs of `𝒟`. -/
def IsDenseModel (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (F : BlockFamily K r) : Prop :=
  UnitValued F ∧
    ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ l : Fin K, ValidGap B l →
      ∀ T : CubeTemplate, Allowed Dm T → ∀ J0 : ℕ, 0 < J0 →
        ∀ ε > 0, ∀ᶠ N in atTop, ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ ε

/-- Finite-dimensional minimax (05:213–226), existence form: on a finite support with weights
`μ ≥ 0`, if `0 ≤ ρ ≤ ν` and `𝒞` is compact convex nonempty, some `F ∈ [0,1]^X` satisfies
`⟨ρ − F, G⟩_μ ≤ sup_{G' ∈ 𝒞} ⟨ν − 1, G'_+⟩_μ` for every `G ∈ 𝒞`. -/
theorem dense_model_minimax {X : Type} [Fintype X] (μ ρ ν : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ ν x) (C : Set (X → ℝ)) (hC : Convex ℝ C) (hCc : IsCompact C)
    (hne : C.Nonempty) :
    ∃ F : X → ℝ, (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ G ∈ C,
      ∑ x, μ x * (ρ x - F x) * G x ≤
        sSup ((fun G' : X → ℝ => ∑ x, μ x * (ν x - 1) * max (G' x) 0) '' C) := by
  exact HindmanSumsProducts.finite_dense_model_minimax μ ρ ν hμ hρ C hC hCc hne

/-- The stage-`Q` test class at a block: valid gap, allowed type of dimension `≤ Q`,
`0 < J₀ ≤ Q`. -/
def StageTest (Dm : Finset (IntegerPolynomial sl)) (B : Block K) (Q : ℕ) (l : Fin K)
    (T : CubeTemplate) (J0 : ℕ) : Prop :=
  ValidGap B l ∧ Allowed Dm T ∧ T.d ≤ Q ∧ 0 < J0 ∧ J0 ≤ Q

/-- The signed clipped tests of stage `Q` at index `N` (05:213–215). -/
def stageClippedTests (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ) (Kc : ℝ) (N : ℕ) :
    Set (ℤ → ℝ) :=
  {G | ∃ (l : Fin K) (T : CubeTemplate) (J0 : ℕ) (I : DualInput MS B T N),
    StageTest Dm B Q l T J0 ∧
      (G = (fun y => clip Kc (dualTest MS B T l J0 N I y)) ∨
        G = (fun y => -clip Kc (dualTest MS B T l J0 N I y)))}

/-- Positive-part bound (05:228–235): for fixed stage `Q`, `K > A_*` (with `d_* = Q`) and
`δ > 0`, `E_{μ_i}(ν − 1) G_+ ≤ 2δ + o(1)` uniformly over the closed convex hull of the signed
clipped stage tests. -/
theorem dense_model_positive_part (MS : MasterScales K As sl Dm) (B : Block K) (Q : ℕ)
    (Kc : ℝ) (hK : dualMomentConstant Q < Kc) (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ G ∈ closure (convexHull ℝ (stageClippedTests MS B Q Kc N)),
        Emu MS.core.parameters N B.1 (fun y => (nu MS.core.parameters N B y - 1) * max (G y) 0) ≤
        2 * δ + ε := by
  intro ε hε
  classical
  let A := MS.core.parameters
  have hApos : 0 < dualMomentConstant Q := by
    unfold dualMomentConstant
    positivity
  have hKpos : 0 < Kc := hApos.trans hK
  have hcont : ContinuousOn (fun x : ℝ => max x 0) (Set.Icc (-Kc) Kc) :=
    (continuous_id.max continuous_const).continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-Kc) Kc (fun x : ℝ => max x 0) hcont δ hδ
  let coeffMass := HindmanSumsProducts.densePolynomialCoefficientL1 p
  have hcoeffMass : 0 ≤ coeffMass := by
    unfold coeffMass HindmanSumsProducts.densePolynomialCoefficientL1
    exact Finset.sum_nonneg fun n hn => abs_nonneg _
  let ηMass : ℝ := ε / (2 * δ)
  let ηPoly : ℝ := ε / (2 * (coeffMass + 1))
  have hηMass : 0 < ηMass := by
    dsimp [ηMass]
    exact div_pos hε (mul_pos (by norm_num) hδ)
  have hηPoly : 0 < ηPoly := by
    dsimp [ηPoly]
    exact div_pos hε (mul_pos (by norm_num) (by linarith [hcoeffMass]))
  have hmassEvent : ∀ᶠ N in atTop,
      |Emu A N B.1 (fun y => nu A N B y - 1)| ≤ ηMass := by
    have hzero := dual_products_orthogonal MS B 0
      (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
      (by intro k; exact Fin.elim0 k) (by intro k; exact Fin.elim0 k)
      (by intro k; exact Fin.elim0 k)
    filter_upwards [hzero ηMass hηMass] with N hN
    simpa using hN (fun k => Fin.elim0 k)
  let Templates : Type := {T : CubeTemplate // Allowed Dm T ∧ T.d ≤ Q}
  letI : Finite Templates := finite_allowed_cubeTemplates Dm
  letI : Fintype Templates := Fintype.ofFinite Templates
  let StageParams : Type :=
    {p : Fin K × Templates × Fin (Q + 1) // ValidGap B p.1 ∧ 0 < p.2.2.val}
  letI : Fintype StageParams := Fintype.ofFinite StageParams
  let stageGap := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) => (pt k).val.1
  let stageTemplate := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) =>
    ((pt k).val.2.1).val
  let stageJ0 := fun {b : ℕ} (pt : Fin b → StageParams) (k : Fin b) =>
    ((pt k).val.2.2).val
  have hprodUniform (b : ℕ) :
      ∀ᶠ N in atTop, ∀ pt : Fin b → StageParams,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
    have hpt : ∀ pt : Fin b → StageParams, ∀ᶠ N in atTop,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
      intro pt
      have hgap : ∀ k, ValidGap B (stageGap pt k) := fun k => (pt k).property.1
      have hT : ∀ k, Allowed Dm (stageTemplate pt k) :=
        fun k => ((pt k).val.2.1).property.1
      have hd : ∀ k, (stageTemplate pt k).d ≤ Q :=
        fun k => ((pt k).val.2.1).property.2
      have hJ0 : ∀ k, 0 < stageJ0 pt k := fun k => (pt k).property.2
      exact dual_products_orthogonal_clipped MS B b (stageGap pt) (stageTemplate pt)
        (stageJ0 pt) hgap hT hJ0 Q hd Kc hK ηPoly hηPoly
    exact Filter.eventually_all.2 hpt
  have hprodDegree : ∀ᶠ N in atTop,
      ∀ b ≤ p.natDegree, ∀ pt : Fin b → StageParams,
        ∀ I : (k : Fin b) → DualInput MS B (stageTemplate pt k) N,
          |Emu A N B.1 (fun y => (nu A N B y - 1) *
            ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
              (stageJ0 pt k) N (I k) y))| ≤ ηPoly := by
    have hfinite : ∀ᶠ N in atTop, ∀ b : Fin (p.natDegree + 1),
        ∀ pt : Fin b.val → StageParams,
          ∀ I : (k : Fin b.val) → DualInput MS B (stageTemplate pt k) N,
            |Emu A N B.1 (fun y => (nu A N B y - 1) *
              ∏ k, clip Kc (dualTest MS B (stageTemplate pt k) (stageGap pt k)
                (stageJ0 pt k) N (I k) y))| ≤ ηPoly :=
      Filter.eventually_all.2 (fun b => hprodUniform b.val)
    filter_upwards [hfinite] with N hN
    intro b hb pt I
    exact hN ⟨b, Nat.lt_succ_of_le hb⟩ pt I
  filter_upwards [hmassEvent, hprodDegree] with N hmassN hprodN
  let tests : Set (ℤ → ℝ) := stageClippedTests MS B Q Kc N
  have hHull : ∀ G ∈ convexHull ℝ tests,
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + ε := by
    intro G hG
    rcases mem_convexHull_iff_exists_fintype.mp hG with
      ⟨τ, hτ, c, q, hc0, hc1, hqmem, hcomb⟩
    letI : Fintype τ := hτ
    have hcL1 : HindmanSumsProducts.denseCoefficientL1 c = 1 :=
      HindmanSumsProducts.denseCoefficientL1_eq_one_of_nonneg c hc0 hc1
    have hqbound (t : τ) (y : ℤ) : |q t y| ≤ Kc := by
      rcases hqmem t with ⟨l, T, J0, I, hStage, hsign⟩
      rcases hsign with hsign | hsign
      · rw [hsign]
        exact clip_abs_le_of_nonneg hKpos.le
      · rw [hsign]
        simpa only [abs_neg] using clip_abs_le_of_nonneg hKpos.le
    have hcombBound (y : ℤ) :
        |HindmanSumsProducts.denseTestCombination q c y| ≤ Kc := by
      unfold HindmanSumsProducts.denseTestCombination
      calc
        |∑ t, c t * q t y| ≤ ∑ t, |c t * q t y| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ t, c t * |q t y| := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [abs_mul, abs_of_nonneg (hc0 t)]
        _ ≤ ∑ t, c t * Kc := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left (hqbound t y) (hc0 t)
        _ = Kc := by
          rw [← Finset.sum_mul, hc1, one_mul]
    have hGval (y : ℤ) : HindmanSumsProducts.denseTestCombination q c y = G y := by
      simpa [HindmanSumsProducts.denseTestCombination, Pi.smul_apply, smul_eq_mul]
        using congrFun hcomb y
    let S := finitePivotSupport A N B.1
    let w : ℤ → ℝ := fun y => mu A N B.1 y
    let f : ℤ → ℝ := fun y => nu A N B y - 1
    have hmono : ∀ (m : ℕ), m ≤ p.natDegree → ∀ s : Fin m → τ,
        |HindmanSumsProducts.denseFinitePairing S w f
          (HindmanSumsProducts.denseTestMonomial q s)| ≤ ηPoly := by
      intro m hm s
      have hmem : ∀ k : Fin m, q (s k) ∈ tests := fun k => hqmem (s k)
      choose l T J0 I hStage hsign using hmem
      let tparam : Fin m → Templates := fun k =>
        ⟨T k, ⟨(hStage k).2.1, (hStage k).2.2.1⟩⟩
      let jparam : Fin m → Fin (Q + 1) := fun k =>
        ⟨J0 k, Nat.lt_succ_of_le (hStage k).2.2.2.2⟩
      let pt : Fin m → StageParams := fun k =>
        ⟨(l k, tparam k, jparam k), ⟨(hStage k).1, (hStage k).2.2.2.1⟩⟩
      have hclip := hprodN m hm pt I
      let clipped : Fin m → ℤ → ℝ := fun k y =>
        clip Kc (dualTest MS B (T k) (l k) (J0 k) N (I k) y)
      let sign : Fin m → ℝ := fun k =>
        if q (s k) = clipped k then 1 else -1
      have hfactor (k : Fin m) (y : ℤ) : q (s k) y = sign k * clipped k y := by
        by_cases hk : q (s k) = clipped k
        · simp [sign, hk]
        · rcases hsign k with hsign | hsign
          · exact False.elim (hk hsign)
          · dsimp [sign]
            rw [if_neg hk]
            rw [hsign]
            ring
      have hsignabs (k : Fin m) : |sign k| = 1 := by
        by_cases hk : q (s k) = clipped k
        · simp [sign, hk]
        · rcases hsign k with hsign | hsign
          · exact False.elim (hk hsign)
          · simp [sign, hk]
      have hsignprod : |∏ k, sign k| = 1 := by
        rw [Finset.abs_prod]
        simp_rw [hsignabs]
        simp
      have hprodEq (y : ℤ) :
          HindmanSumsProducts.denseTestMonomial q s y =
            (∏ k, sign k) * ∏ k, clipped k y := by
        unfold HindmanSumsProducts.denseTestMonomial
        calc
          (∏ k, q (s k) y) = ∏ k, sign k * clipped k y := by
            apply Finset.prod_congr rfl
            intro k hk
            exact hfactor k y
          _ = (∏ k, sign k) * ∏ k, clipped k y := Finset.prod_mul_distrib
      have hraw : |Emu A N B.1 (fun y => f y *
          HindmanSumsProducts.denseTestMonomial q s y)| ≤ ηPoly := by
        have hEq : Emu A N B.1 (fun y => f y *
            HindmanSumsProducts.denseTestMonomial q s y) =
            (∏ k, sign k) * Emu A N B.1 (fun y => f y * ∏ k, clipped k y) := by
          calc
            _ = Emu A N B.1 (fun y => (∏ k, sign k) * (f y * ∏ k, clipped k y)) := by
              apply Emu_congr
              intro y
              rw [hprodEq y]
              ring
            _ = _ := Emu_smul A N B.1 (∏ k, sign k) _
        rw [hEq, abs_mul, hsignprod, one_mul]
        exact hclip
      have hpair : HindmanSumsProducts.denseFinitePairing S w f
          (HindmanSumsProducts.denseTestMonomial q s) =
            Emu A N B.1 (fun y => f y * HindmanSumsProducts.denseTestMonomial q s y) := by
        rw [Emu_eq_sum_finitePivotSupport]
        unfold HindmanSumsProducts.denseFinitePairing S w f
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [hpair]
      exact hraw
    have hpolyPair :
        |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y))|
            ≤ coeffMass * ηPoly := by
      exact HindmanSumsProducts.denseAbsPolynomialPairing_le S hcL1 hmono
    have hpointErr (y : ℤ) :
        |max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)| ≤ δ := by
      have hyIcc : HindmanSumsProducts.denseTestCombination q c y ∈ Set.Icc (-Kc) Kc :=
        abs_le.mp (hcombBound y)
      have h := hp _ hyIcc
      calc
        |max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)| =
            |max (HindmanSumsProducts.denseTestCombination q c y) 0 -
              p.eval (HindmanSumsProducts.denseTestCombination q c y)| := by rw [← hGval y]
        _ = |p.eval (HindmanSumsProducts.denseTestCombination q c y) -
              max (HindmanSumsProducts.denseTestCombination q c y) 0| := abs_sub_comm _ _
        _ ≤ δ := h.le
    have herrorPair :
        |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))|
            ≤ δ * ∑ y ∈ S, w y * |f y| := by
      apply HindmanSumsProducts.denseAbsPairing_le_mul_weightedMass S w f
        (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))
        (fun y hy => harmonicLaw_nonneg A N B.1 y) (fun y => hpointErr y)
    have hmassPoint (y : ℤ) : |f y| ≤ 1 + nu A N B y := by
      have hν := nu_nonneg A N B y
      change |nu A N B y - 1| ≤ 1 + nu A N B y
      rw [abs_le]
      constructor <;> linarith
    have hmassBound : ∑ y ∈ S, w y * |f y| ≤ 2 + ηMass := by
      have hEabs := Emu_mono A N B.1 hmassPoint
      have hEone := Emu_const_one_eq_one MS N B.1
      have hEadd := Emu_add A N B.1 (fun _ => (1 : ℝ)) (fun y => nu A N B y)
      have hEsub := Emu_sub A N B.1 (fun y => nu A N B y) (fun _ => (1 : ℝ))
      have hEadd' : Emu A N B.1 (fun y => 1 + nu A N B y) =
          1 + Emu A N B.1 (fun y => nu A N B y) := by
        rw [hEone] at hEadd
        exact hEadd
      have hEsub' : Emu A N B.1 (fun y => nu A N B y - 1) =
          Emu A N B.1 (fun y => nu A N B y) - 1 := by
        rw [hEone] at hEsub
        exact hEsub
      have hmean : Emu A N B.1 (fun y => 1 + nu A N B y) =
          2 + Emu A N B.1 (fun y => nu A N B y - 1) := by
        linarith [hEadd', hEsub']
      have hνerr : Emu A N B.1 (fun y => nu A N B y - 1) ≤ ηMass :=
        (le_abs_self _).trans hmassN
      have hsumE : (∑ y ∈ S, w y * |f y|) =
          Emu A N B.1 (fun y => |f y|) := by
        rw [Emu_eq_sum_finitePivotSupport]
      rw [hsumE]
      calc
        Emu A N B.1 (fun y => |f y|) ≤ Emu A N B.1 (fun y => 1 + nu A N B y) := hEabs
        _ = 2 + Emu A N B.1 (fun y => nu A N B y - 1) := hmean
        _ ≤ 2 + ηMass := by linarith
    have hsplit :
        HindmanSumsProducts.denseFinitePairing S w f (fun y => max (G y) 0) =
          HindmanSumsProducts.denseFinitePairing S w f
              (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y)) +
            HindmanSumsProducts.denseFinitePairing S w f
              (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)) := by
      unfold HindmanSumsProducts.denseFinitePairing
      calc
        (∑ y ∈ S, w y * f y * max (G y) 0) =
            ∑ y ∈ S, (w y * f y * p.eval (HindmanSumsProducts.denseTestCombination q c y) +
              w y * f y * (max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = _ := Finset.sum_add_distrib
    have hpolyLe : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => p.eval (HindmanSumsProducts.denseTestCombination q c y)) ≤ coeffMass * ηPoly :=
      (le_abs_self _).trans hpolyPair
    have herrLe : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y)) ≤
          δ * (2 + ηMass) := by
      calc
        _ ≤ |HindmanSumsProducts.denseFinitePairing S w f
          (fun y => max (G y) 0 - p.eval (HindmanSumsProducts.denseTestCombination q c y))| := le_abs_self _
        _ ≤ δ * ∑ y ∈ S, w y * |f y| := herrorPair
        _ ≤ δ * (2 + ηMass) := mul_le_mul_of_nonneg_left hmassBound (le_of_lt hδ)
    have hcoeffBound : coeffMass * ηPoly ≤ ε / 2 := by
      dsimp [ηPoly]
      have hden : 0 < 2 * (coeffMass + 1) := by positivity
      field_simp [ne_of_gt hden]
      have hc0 : 0 ≤ coeffMass := hcoeffMass
      nlinarith [hε]
    have herrBound : δ * (2 + ηMass) ≤ 2 * δ + ε / 2 := by
      dsimp [ηMass]
      field_simp [ne_of_gt hδ] <;> norm_num
    have hpairBound : HindmanSumsProducts.denseFinitePairing S w f
        (fun y => max (G y) 0) ≤ 2 * δ + ε := by
      rw [hsplit]
      linarith [hpolyLe, herrLe, hcoeffBound, herrBound]
    have hEmuPair : Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) =
        HindmanSumsProducts.denseFinitePairing S w f (fun y => max (G y) 0) := by
      rw [Emu_eq_sum_finitePivotSupport]
      unfold HindmanSumsProducts.denseFinitePairing S w f
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [hEmuPair]
    exact hpairBound
  have hcont : Continuous (fun G : ℤ → ℝ =>
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0)) := by
    have heq : (fun G : ℤ → ℝ =>
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0)) =
        fun G => ∑ y ∈ finitePivotSupport A N B.1,
          mu A N B.1 y * ((nu A N B y - 1) * max (G y) 0) := by
      funext G
      rw [Emu_eq_sum_finitePivotSupport]
    rw [heq]
    fun_prop
  let good : Set (ℤ → ℝ) := {G | Emu A N B.1
    (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + ε}
  have hgoodClosed : IsClosed good := isClosed_Iic.preimage hcont
  have hHullSubset : convexHull ℝ (stageClippedTests MS B Q Kc N) ⊆ good := hHull
  have hclosure := closure_minimal hHullSubset hgoodClosed
  intro G hG
  exact hclosure hG

/-- One stage of Proposition `prop:dense-model` (05:209–240): for a fixed stage `Q` there are
`[0,1]`-valued models with error at most `1/(Q+1)` against every stage test, for all large `N`,
uniformly over the finitely many master blocks, scale labels, colours and inputs. -/
theorem dense_model_stage (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) (Q : ℕ) :
    ∃ F : BlockFamily K r, UnitValued F ∧ ∀ᶠ N in atTop,
      ∀ (B : Block K), ∀ a ∈ As, ∀ c : Fin r, ∀ (l : Fin K) (T : CubeTemplate) (J0 : ℕ),
        StageTest Dm B Q l T J0 → ∀ I : DualInput MS B T N,
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B T l J0 N I y)| ≤ 1 / ((Q : ℝ) + 1) := by
  classical
  let A := MS.core.parameters
  let Kc := dualMomentConstant Q + 1
  have hK : dualMomentConstant Q < Kc := by dsimp [Kc]; linarith
  have hKpos : 0 < Kc := by
    have hA : 0 < dualMomentConstant Q := by
      unfold dualMomentConstant
      positivity
    dsimp [Kc]
    linarith
  let targetErr : ℝ := 1 / ((Q : ℝ) + 1)
  let δ : ℝ := targetErr / 8
  let εpos : ℝ := targetErr / 4
  let εclip : ℝ := targetErr / 2
  have hTargetErr : 0 < targetErr := by dsimp [targetErr]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hεpos : 0 < εpos := by dsimp [εpos]; positivity
  have hεclip : 0 < εclip := by dsimp [εclip]; positivity
  have herrorSplit : 2 * δ + εpos + εclip = targetErr := by
    dsimp [targetErr, δ, εpos, εclip]
    ring
  let stageTests (N : ℕ) (B : Block K) : Set (ℤ → ℝ) :=
    stageClippedTests MS B Q Kc N
  let Support (N : ℕ) (B : Block K) := finitePivotSupport A N B.1
  letI (N : ℕ) (B : Block K) : Fintype (Support N B) :=
    Finset.fintypeCoeSort (finitePivotSupport A N B.1)
  let restrict (N : ℕ) (B : Block K) :
      (ℤ → ℝ) →ₗ[ℝ] (Support N B → ℝ) :=
    { toFun := fun (G : ℤ → ℝ) (x : Support N B) => G (x : ℤ)
      map_add' := by
        intro G H
        funext x
        rfl
      map_smul' := by
        intro a G
        funext x
        rfl }
  let restrictedTests (N : ℕ) (B : Block K) : Set (Support N B → ℝ) :=
    restrict N B '' stageTests N B
  let stageClass (N : ℕ) (B : Block K) : Set (Support N B → ℝ) :=
    closure (convexHull ℝ (restrictedTests N B))
  let stagePositive (N : ℕ) (B : Block K) (G : Support N B → ℝ) : ℝ :=
    ∑ x : Support N B, mu A N B.1 x * (nu A N B x - 1) * max (G x) 0
  let templates : Type := {T : CubeTemplate // Allowed Dm T ∧ T.d ≤ Q}
  letI : Finite templates := finite_allowed_cubeTemplates Dm
  letI : Fintype templates := Fintype.ofFinite templates
  let StageParam (B : Block K) : Type :=
    {p : Fin K × templates × Fin (Q + 1) // ValidGap B p.1 ∧ 0 < p.2.2.val}
  letI (B : Block K) : Fintype (StageParam B) := Fintype.ofFinite (StageParam B)
  letI : Fintype (Block K) := inferInstance
  let AllStageParams : Type := Σ B : Block K, StageParam B
  letI : Fintype (AllStageParams) := inferInstance
  have hposAll : ∀ᶠ N in atTop, ∀ B : Block K, ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos := by
    apply Filter.eventually_all.2
    intro B
    exact dense_model_positive_part MS B Q Kc hK δ hδ εpos hεpos
  let allGap := fun p : AllStageParams => p.2.val.1
  let allTemplate := fun p : AllStageParams => p.2.val.2.1.val
  let allJ0 := fun p : AllStageParams => p.2.val.2.2.val
  have hclipEach (p : AllStageParams) : ∀ᶠ N in atTop,
      ∀ I : DualInput MS p.1 (allTemplate p) N,
        Emu A N p.1.1 (fun y => (1 + nu A N p.1 y) *
          |dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y -
            clip Kc (dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y)| ^ 1) ≤ εclip := by
    let B := p.1
    let P := p.2
    exact dual_clipping_error MS B (allGap p) (allTemplate p) (allJ0 p)
      P.property.1 P.val.2.1.property.1 P.property.2 Q P.val.2.1.property.2
      Kc hK 1 (by norm_num) εclip hεclip
  have hclipAll : ∀ᶠ N in atTop, ∀ p : AllStageParams,
      ∀ I : DualInput MS p.1 (allTemplate p) N,
        Emu A N p.1.1 (fun y => (1 + nu A N p.1 y) *
          |dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y -
            clip Kc (dualTest MS p.1 (allTemplate p) (allGap p) (allJ0 p) N I y)| ^ 1) ≤ εclip := by
    exact Filter.eventually_all.2 hclipEach
  let stagePsiEq (N : ℕ) (B : Block K) (G : ℤ → ℝ) :
      Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) =
        stagePositive N B (restrict N B G) := by
    rw [Emu_eq_sum_finitePivotSupportSort]
    unfold stagePositive
    apply Fintype.sum_congr
    intro x
    dsimp [restrict]
    ring
  have hstageClassPos {N : ℕ} {B : Block K}
      (hpos : ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos) :
      ∀ G ∈ stageClass N B, stagePositive N B G ≤ 2 * δ + εpos := by
    have hcont : Continuous (stagePositive N B) := by
      unfold stagePositive
      simpa using continuous_finsetSum (Finset.univ : Finset (Support N B))
        (fun x hx => by fun_prop)
    let good : Set (Support N B → ℝ) := {G | stagePositive N B G ≤ 2 * δ + εpos}
    have hgoodClosed : IsClosed good := isClosed_Iic.preimage hcont
    have himage : restrict N B '' convexHull ℝ (stageTests N B) =
        convexHull ℝ (restrictedTests N B) :=
      (restrict N B).image_convexHull (stageTests N B)
    have hsub : convexHull ℝ (restrictedTests N B) ⊆ good := by
      intro G hG
      rw [← himage] at hG
      rcases hG with ⟨G0, hG0, rfl⟩
      have hG0' : G0 ∈ closure (convexHull ℝ (stageTests N B)) := subset_closure hG0
      change stagePositive N B (restrict N B G0) ≤ 2 * δ + εpos
      rw [← stagePsiEq N B G0]
      exact hpos G0 hG0'
    have hclosure := closure_minimal hsub hgoodClosed
    exact hclosure
  have hmodelExists (N : ℕ) (B : Block K) (a : ℚ) (c : Fin r) :
      ∃ F0 : ℤ → ℝ, (∀ y, F0 y ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ G ∈ stageTests N B,
          Emu A N B.1 (fun y => (rho MS.core.parameters χ N B a c y - F0 y) * G y) ≤
            sSup ((stagePositive N B) '' (stageClass N B)) := by
    classical
    let S := stageTests N B
    let C := stageClass N B
    by_cases hS : S.Nonempty
    · have hboxConv : Convex ℝ (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        convex_Icc _ _
      have hboxClosed : IsClosed (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        isClosed_Icc
      have hboxCompact : IsCompact (Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc)) :=
        isCompact_Icc
      have hrestrictedAbs (G0 : ℤ → ℝ) (hG0 : G0 ∈ stageTests N B)
          (x : Support N B) : |(restrict N B G0) x| ≤ Kc := by
        rcases hG0 with ⟨l, T, J0, I, hStage, hsign | hsign⟩
        · have hb : |clip Kc (dualTest MS B T l J0 N I (x : ℤ))| ≤ Kc :=
            clip_abs_le_of_nonneg hKpos.le
          dsimp [restrict]
          rw [hsign]
          exact hb
        · have hb : |clip Kc (dualTest MS B T l J0 N I (x : ℤ))| ≤ Kc :=
            clip_abs_le_of_nonneg hKpos.le
          dsimp [restrict]
          rw [hsign]
          simpa only [abs_neg] using hb
      have htestBound : restrictedTests N B ⊆
          Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc) := by
        rintro G ⟨G0, hG0, rfl⟩
        refine Set.mem_Icc.mpr ⟨?_, ?_⟩
        · intro x
          exact (abs_le.mp (hrestrictedAbs G0 hG0 x)).1
        · intro x
          exact (abs_le.mp (hrestrictedAbs G0 hG0 x)).2
      have hCsub : C ⊆ Set.Icc (fun _ : Support N B => -Kc) (fun _ => Kc) :=
        closure_minimal
          (hboxConv.convexHull_subset_iff.mpr htestBound) hboxClosed
      have hCcompact : IsCompact C :=
        hboxCompact.of_isClosed_subset isClosed_closure hCsub
      have hCconv : Convex ℝ C :=
        (convex_convexHull ℝ (restrictedTests N B)).closure
      have hCnonempty : C.Nonempty := by
        rcases hS with ⟨G, hG⟩
        exact ⟨restrict N B G,
          subset_closure (subset_convexHull ℝ _ ⟨G, hG, rfl⟩)⟩
      obtain ⟨F0, hF0, hF0ineq⟩ := finitePivot_minimax A N B.1
        (fun y => rho MS.core.parameters χ N B a c y) (fun y => nu A N B y)
        (fun y => rho_bounds A χ N B a c y) C hCconv hCcompact hCnonempty
      refine ⟨F0, hF0, ?_⟩
      intro G hG
      have hGmem : restrict N B G ∈ C :=
        subset_closure (subset_convexHull ℝ _ ⟨G, hG, rfl⟩)
      have hmin := hF0ineq (restrict N B G) hGmem
      have hpair : Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F0 y) * G y) =
            ∑ x : Support N B, mu A N B.1 (x : ℤ) *
              (rho MS.core.parameters χ N B a c (x : ℤ) - F0 (x : ℤ)) *
                (restrict N B G) x := by
        rw [Emu_eq_sum_finitePivotSupportSort]
        apply Fintype.sum_congr
        intro x
        dsimp [restrict]
        ring
      rw [hpair]
      exact hmin
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro y
        exact ⟨le_rfl, zero_le_one⟩
      · intro G hG
        exact False.elim (hS ⟨G, hG⟩)
  let model : ℕ → Block K → ℚ → Fin r → ℤ → ℝ :=
    fun N B a c => Classical.choose (hmodelExists N B a c)
  have hmodelSpec (N : ℕ) (B : Block K) (a : ℚ) (c : Fin r) :=
    Classical.choose_spec (hmodelExists N B a c)
  let F : BlockFamily K r := model
  have hFunit : UnitValued F := by
    intro N B a c y
    exact (hmodelSpec N B a c).1 y
  have hposEvent : ∀ᶠ N in atTop, ∀ B : Block K,
      ∀ G ∈ closure (convexHull ℝ (stageTests N B)),
        Emu A N B.1 (fun y => (nu A N B y - 1) * max (G y) 0) ≤ 2 * δ + εpos :=
    hposAll
  have hclipEvent := hclipAll
  refine ⟨F, hFunit, ?_⟩
  filter_upwards [hposEvent, hclipEvent] with N hposN hclipN
  intro B a ha c l T J0 hStage I
  let hDual : ℤ → ℝ := dualTest MS B T l J0 N I
  let hClip : ℤ → ℝ := fun y => clip Kc (hDual y)
  have hClipMem : hClip ∈ stageTests N B :=
    ⟨l, T, J0, I, hStage, Or.inl rfl⟩
  have hNegClipMem : (fun y => -hClip y) ∈ stageTests N B :=
    ⟨l, T, J0, I, hStage, Or.inr rfl⟩
  have hclassBound := hstageClassPos (N := N) (B := B) (hposN B)
  have hCbound : ∀ G ∈ stageClass N B, stagePositive N B G ≤ 2 * δ + εpos :=
    hclassBound
  have hCnonempty : (stageClass N B).Nonempty := by
    exact ⟨restrict N B hClip,
      subset_closure (subset_convexHull ℝ _ ⟨hClip, hClipMem, rfl⟩)⟩
  have hValuesNonempty : ((stagePositive N B) '' (stageClass N B)).Nonempty :=
    hCnonempty.image _
  have hsupBound : sSup ((stagePositive N B) '' (stageClass N B)) ≤ 2 * δ + εpos := by
    apply csSup_le hValuesNonempty
    rintro v ⟨G, hG, rfl⟩
    exact hCbound G hG
  have hplusBound : Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) ≤
        2 * δ + εpos := by
    exact ((hmodelSpec N B a c).2 hClip hClipMem).trans hsupBound
  have hnegEq : Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * (-hClip y)) =
        -Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) := by
    calc
      _ = Emu A N B.1 (fun y => (-1 : ℝ) *
          ((rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)) := by
        apply Emu_congr
        intro y
        ring
      _ = (-1 : ℝ) * Emu A N B.1
          (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) :=
        Emu_smul A N B.1 (-1) _
      _ = _ := by ring
  have hnegBound : -Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) ≤
        2 * δ + εpos := by
    rw [← hnegEq]
    exact ((hmodelSpec N B a c).2 (fun y => -hClip y) hNegClipMem).trans hsupBound
  have hclipCorrelation : |Emu A N B.1
      (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)| ≤
        2 * δ + εpos := by
    rw [abs_le]
    constructor
    · linarith [hnegBound]
    · exact hplusBound
  let tparam : templates := ⟨T, ⟨hStage.2.1, hStage.2.2.1⟩⟩
  let jparam : Fin (Q + 1) := ⟨J0, Nat.lt_succ_of_le hStage.2.2.2.2⟩
  let param : StageParam B :=
    ⟨(l, tparam, jparam), ⟨hStage.1, hStage.2.2.2.1⟩⟩
  let allParam : AllStageParams := ⟨B, param⟩
  have hclipError : Emu A N B.1 (fun y => (1 + nu A N B y) *
      |hDual y - hClip y|) ≤ εclip := by
    have h := hclipN allParam (by
      simpa [allParam, param, tparam, allTemplate] using I)
    simpa [allParam, param, tparam, jparam, allGap, allTemplate, allJ0,
      hDual, hClip, pow_one] using h
  have hrhoF (y : ℤ) :
      |rho MS.core.parameters χ N B a c y - F N B a c y| ≤ 1 + nu A N B y := by
    have hr := rho_bounds A χ N B a c y
    have hν := nu_nonneg A N B y
    have hFv := hFunit N B a c y
    rw [abs_le]
    constructor <;> rcases Set.mem_Icc.mp hFv with ⟨hF0, hF1⟩ <;> linarith
  have herrAbs : |Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| ≤
        Emu A N B.1 (fun y => (1 + nu A N B y) * |hDual y - hClip y|) := by
    calc
      _ ≤ Emu A N B.1 (fun y => |(rho MS.core.parameters χ N B a c y - F N B a c y) *
          (hDual y - hClip y)|) := Emu_abs_le A N B.1 _
      _ ≤ Emu A N B.1 (fun y => (1 + nu A N B y) * |hDual y - hClip y|) := by
        apply Emu_mono A N B.1
        intro y
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hrhoF y) (abs_nonneg _)
  have herrBound : |Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| ≤ εclip :=
    herrAbs.trans hclipError
  have hsplit : Emu A N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * hDual y) =
      Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) +
      Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y)) := by
    rw [← Emu_add]
    congr 1
    funext y
    ring
  calc
    |Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hDual y)| =
      |Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y) +
       Emu A N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| := by rw [hsplit]
    _ ≤ |Emu A N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * hClip y)| +
        |Emu A N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * (hDual y - hClip y))| := abs_add_le _ _
    _ ≤ (2 * δ + εpos) + εclip := add_le_add hclipCorrelation herrBound
    _ = targetErr := herrorSplit

/-- Proposition `prop:dense-model` (05:199–207): bounded dense models exist.  Proof: the stages
`dense_model_stage Q`, diagonalized with `Q = Q(N)` increasing slowly (05:240–247). -/
theorem bounded_dense_models (MS : MasterScales K As sl Dm) (χ : ℕ → Fin r) :
    ∃ F : BlockFamily K r, IsDenseModel MS χ F := by
  classical
  let stageFamily : ℕ → BlockFamily K r := fun q =>
    Classical.choose (dense_model_stage MS χ q)
  have stageSpec (q : ℕ) := Classical.choose_spec (dense_model_stage MS χ q)
  let cutoff : ℕ → ℕ := fun q =>
    Classical.choose (Filter.eventually_atTop.1 (stageSpec q).2)
  have cutoffSpec (q : ℕ) (N : ℕ) (hN : cutoff q ≤ N) :=
    Classical.choose_spec (Filter.eventually_atTop.1 (stageSpec q).2) N hN
  let candidates (N : ℕ) : Finset ℕ :=
    insert 0 ((Finset.range (N + 1)).filter (fun q => cutoff q ≤ N))
  let slow (N : ℕ) : ℕ := (candidates N).max' (by simp [candidates])
  let F : BlockFamily K r := fun N B a c y => stageFamily (slow N) N B a c y
  have hUnit : UnitValued F := by
    intro N B a c y
    exact (stageSpec (slow N)).1 N B a c y
  refine ⟨F, ?_⟩
  change UnitValued F ∧ _
  refine ⟨hUnit, ?_⟩
  intro B a ha c l hl T hT J0 hJ0 ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ε)
  have hRerr : 1 / ((R : ℝ) + 1) ≤ ε := by
    have hmul := mul_lt_mul_of_pos_left hR hε
    have hεR : 1 < ε * (R : ℝ) := by
      simpa [hε.ne', mul_comm] using hmul
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) + 1)]
    nlinarith [hεR]
  let qmin : ℕ := max (max T.d J0) R
  have hJ0le : J0 ≤ qmin := by
    dsimp [qmin]
    exact (Nat.le_max_right T.d J0).trans (Nat.le_max_left _ _)
  have hqminPos : 0 < qmin := lt_of_lt_of_le hJ0 hJ0le
  have hlarge : ∀ᶠ N in atTop, max qmin (cutoff qmin) ≤ N := by
    exact Filter.eventually_atTop.2 ⟨max qmin (cutoff qmin), fun _ hN => hN⟩
  have hslowLarge : ∀ᶠ N in atTop,
      qmin ≤ slow N ∧ cutoff (slow N) ≤ N := by
    filter_upwards [hlarge] with N hN
    have hqminN : qmin ≤ N := (Nat.le_max_left _ _).trans hN
    have hcutminN : cutoff qmin ≤ N := (Nat.le_max_right _ _).trans hN
    have hqminRange : qmin ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hqminN)
    have hqminCandidate : qmin ∈ candidates N :=
      Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hqminRange, hcutminN⟩)
    have hge : qmin ≤ slow N := (candidates N).le_max' qmin hqminCandidate
    have hqPos : 0 < slow N := lt_of_lt_of_le hqminPos hge
    have hmaxMem : slow N ∈ candidates N :=
      (candidates N).max'_mem (by simp [candidates])
    rcases Finset.mem_insert.mp hmaxMem with hzero | hfiltered
    · omega
    · exact ⟨hge, (Finset.mem_filter.mp hfiltered).2⟩
  filter_upwards [hslowLarge] with N hN
  intro I
  have hmodel := cutoffSpec (slow N) N hN.2
  have hdim : T.d ≤ slow N := by
    dsimp [qmin] at hN
    exact (Nat.le_max_left T.d J0).trans ((Nat.le_max_left _ _).trans hN.1)
  have hJ0slow : J0 ≤ slow N := by
    exact hJ0le.trans hN.1
  have hJ0Q : J0 ≤ slow N := hJ0slow
  have hStage : StageTest Dm B (slow N) l T J0 :=
    ⟨hl, hT, hdim, hJ0, hJ0Q⟩
  have hbound := hmodel B a ha c l T J0 hStage
  have hRle : R ≤ slow N := by
    dsimp [qmin] at hN
    exact (Nat.le_max_right (max T.d J0) R).trans hN.1
  have hden : (R : ℝ) + 1 ≤ (slow N : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hRle
  have hsmall : 1 / ((slow N : ℝ) + 1) ≤ ε :=
    (one_div_le_one_div_of_le (by positivity) hden).trans hRerr
  exact (hbound I).trans hsmall

/-! ### Lemma `lem:nilsequence-testing` (05:275–353) -/

/-- `y` lies within `width` of an endpoint of its `R`-interval `[kR, (k+1)R)`. -/
def InBoundaryStrip (R width : ℕ) (y : ℤ) : Prop :=
  y % (R : ℤ) ≤ (width : ℤ) ∨ (R : ℤ) ≤ y % (R : ℤ) + (width : ℤ)

/-- Indicator of `InBoundaryStrip`. -/
def boundaryIndicator (R width : ℕ) (y : ℤ) : ℝ := by
  classical
  exact if InBoundaryStrip R width y then 1 else 0

/-- Recipes realized as dual tests (05:287–323): for a fixed menu of step `≤ s`, Lipschitz bound
and accuracy `δ`, there are finitely many scalars `λ_t` (independent of `J₀`, `N` and the
family) such that, for every fixed `J₀` and all large `N`, every representing family at gap `l`
is reconstructed within `δ`, at every root farther than `(s+1)R_l/J₀` from the ends of its
`R_l`-interval, by `∑_t λ_t 𝒟_t` with dual tests of the extra type (dimension `s+1`, modulus `M`),
`e = 1` and inputs bounded by `1`.  Rests on `Charted.cube_corner_recipes`. -/
theorem nilsequence_recipe_tests (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n₀ : ℕ) (coeff : Fin n₀ → ℝ), ∀ J0 : ℕ, 0 < J0 → ∀ᶠ N in atTop,
      ∀ Φ : RepFamily MS.core.parameters l Fm Km,
        ∃ I : Fin n₀ → DualInput MS B (extraTemplate s) N,
          (∀ t p, (I t).e p = 1) ∧ (∀ t ω p y, |(I t).g ω p y| ≤ 1) ∧
          ∀ y : ℤ,
            ¬ InBoundaryStrip (MS.core.parameters.H N l)
              ((s + 1) * MS.core.parameters.H N l / J0) y →
            |Φ.eval N y - ∑ t, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y| ≤ δ := by
  classical
  obtain ⟨m, Recipes, hRecipes⟩ :=
    HindmanSumsProducts.Charted.cube_corner_recipes Fm (1 : ℝ) Km δ hδ
  have hobsBound (P : CosetPiece Fm Km) : ‖P.obs‖ ≤ 1 := by
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro z
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(P.range z).1], (P.range z).2⟩
  have hselectExists (P : CosetPiece Fm Km) :
      ∃ ρ : Fin (m P.index), ∀ (g : Fm.G P.index)
        (x : Fm.G P.index ⧸ Fm.Γ P.index) (k : ℤ) (v : Fin (s + 1) → ℤ),
          |P.obs (g ^ k • x) - (Recipes P.index ρ).eval Fm
            (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ δ := by
    exact hRecipes P.index P.obs (hobsBound P) P.lip
  let selected (P : CosetPiece Fm Km) : Fin (m P.index) :=
    Classical.choose (hselectExists P)
  have hselected (P : CosetPiece Fm Km) := Classical.choose_spec (hselectExists P)
  let nTerms : ℕ := ∑ i : Fin Fm.size, ∑ j : Fin (m i), (Recipes i j).terms
  let RecipeIndex : Type :=
    Σ i : Fin Fm.size, Σ j : Fin (m i), Fin nTerms
  let n₀ : ℕ := Fintype.card RecipeIndex
  let enum : Fin n₀ ≃ RecipeIndex := (Fintype.equivFin RecipeIndex).symm
  let coeffMass (i : Fin Fm.size) (n : ℕ) : ℝ :=
    ∑ j : Fin (m i),
      if h : n < (Recipes i j).terms then
        |(Recipes i j).coeff ⟨n, h⟩|
      else 0
  let coeffQ (q : RecipeIndex) : ℝ :=
    if h : q.2.2.val < (Recipes q.1 q.2.1).terms then
      |(Recipes q.1 q.2.1).coeff ⟨q.2.2.val, h⟩|
    else 0
  let coeff : Fin n₀ → ℝ := fun t => coeffQ (enum t)
  refine ⟨n₀, coeff, ?_⟩
  intro J0 hJ0
  let A := MS.core.parameters
  let p0 : Fin (extraTemplate s).q → ℕ := extraTemplateEmptyTuple s
  have hmodulus (N : ℕ) : (extraTemplate s).modulus (corrScales MS) N p0 = A.M N := by
    have heval : evalIntegerPolynomial (extraTemplate s).D (fun i => (p0 i : ℤ)) = 1 := by
      change (MvPolynomial.eval (fun i => (p0 i : ℤ))) (extraTemplate s).D = 1
      rw [show (extraTemplate s).D = 1 by rfl]
      exact map_one _
    change A.M N * roughPart (N + 1)
      (evalIntegerPolynomial (extraTemplate s).D (fun i => (p0 i : ℤ))) = A.M N
    rw [heval]
    simp [roughPart]
  have hlengthEventually : ∀ᶠ N in atTop,
      0 < (extraTemplate s).length (corrScales MS) l J0 N p0 := by
    have hscale := gapScale_multiple_le_eventually A l J0
    filter_upwards [hscale] with N hscale
    have hden : 0 < J0 * A.M N := Nat.mul_pos hJ0 (A.Mpos N)
    have hdiv : 0 < A.H N l / (J0 * A.M N) := Nat.div_pos hscale hden
    have hlength : (extraTemplate s).length (corrScales MS) l J0 N p0 =
        A.H N l / (J0 * A.M N) := by
      change A.H N l / (J0 * (extraTemplate s).modulus (corrScales MS) N p0) = _
      rw [hmodulus N]
    rw [hlength]
    exact hdiv
  filter_upwards [hlengthEventually] with N hlength
  intro Φ
  let Pof (z : ℤ) : CosetPiece Fm Km :=
    Φ.piece N (z / (A.H N l : ℤ)) (z % (A.M N : ℤ))
  let root0 : Fin (s + 1) := ⟨0, by omega⟩
  let rootFace : Finset (Fin (s + 1)) := {root0}
  have hrootFace : rootFace ∈
      (Finset.univ : Finset (Finset (Fin (s + 1)))).erase ∅ := by
    simp [rootFace, root0]
  have hcoeffMassNonneg (i : Fin Fm.size) (n : ℕ) : 0 ≤ coeffMass i n := by
    dsimp [coeffMass]
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  have hcoeffLeMass (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) :
      |(Recipes P.index (selected P)).coeff ⟨n, hn⟩| ≤ coeffMass P.index n := by
    have hsum := Finset.single_le_sum
      (f := fun j : Fin (m P.index) =>
        if h : n < (Recipes P.index j).terms then
          |(Recipes P.index j).coeff ⟨n, h⟩| else 0)
      (fun j hj => by split_ifs <;> positivity)
      (Finset.mem_univ (selected P))
    simpa [coeffMass, hn] using hsum
  let scaleFor (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) : ℝ :=
    if h : coeffMass P.index n = 0 then 0 else
      (Recipes P.index (selected P)).coeff ⟨n, hn⟩ / coeffMass P.index n
  have hscaleFor (P : CosetPiece Fm Km) (n : ℕ)
      (hn : n < (Recipes P.index (selected P)).terms) : |scaleFor P n hn| ≤ 1 := by
    by_cases hzero : coeffMass P.index n = 0
    · have hcoeffZero : (Recipes P.index (selected P)).coeff ⟨n, hn⟩ = 0 := by
        have hle := hcoeffLeMass P n hn
        have habs : |(Recipes P.index (selected P)).coeff ⟨n, hn⟩| = 0 := by
          apply le_antisymm
          · simpa [hzero] using hle
          · exact abs_nonneg _
        exact abs_eq_zero.mp habs
      simp [scaleFor, hzero, hcoeffZero]
    · have hpos : 0 < coeffMass P.index n := lt_of_le_of_ne
        (hcoeffMassNonneg P.index n) (Ne.symm hzero)
      have hscaleEq : scaleFor P n hn =
          (Recipes P.index (selected P)).coeff ⟨n, hn⟩ / coeffMass P.index n := by
        simp [scaleFor, hzero]
      rw [hscaleEq, abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).2 (hcoeffLeMass P n hn)
  let inputAt (q : RecipeIndex) (ω : Finset (Fin (s + 1)))
      (p : Fin 0 → ℕ) (z : ℤ) : ℝ := by
    classical
    let P := Pof z
    by_cases hi : q.1 = P.index
    · by_cases hn : q.2.2.val < (Recipes P.index (selected P)).terms
      · let t : Fin (Recipes P.index (selected P)).terms := ⟨q.2.2.val, hn⟩
        let f := (Recipes P.index (selected P)).factor t ω
          (P.g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)
        by_cases hω : ω = rootFace
        · exact f * scaleFor P q.2.2.val hn
        · exact f
      · exact 0
    · exact 0
  have hinputBound (q : RecipeIndex) (ω : Finset (Fin (s + 1)))
      (p : Fin 0 → ℕ) (z : ℤ) : |inputAt q ω p z| ≤ 1 := by
    classical
    unfold inputAt
    dsimp [extraTemplate] at *
    split_ifs with hindex hterm hface
    · rw [abs_mul]
      have hfac : |(Recipes (Pof z).index (selected (Pof z))).factor
          ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)| ≤ 1 :=
        (Recipes (Pof z).index (selected (Pof z))).bound ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)
      calc
        _ ≤ |(Recipes (Pof z).index (selected (Pof z))).factor
            ⟨q.2.2.val, hterm⟩ ω
            ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hscaleFor (Pof z) q.2.2.val hterm)
        _ ≤ 1 := hfac
    · simpa [extraTemplate] using
        (Recipes (Pof z).index (selected (Pof z))).bound
          ⟨q.2.2.val, hterm⟩ ω
          ((Pof z).g ^ ((z - z % (A.M N : ℤ)) / (A.M N : ℤ)) • (Pof z).x)
    · simp
    · simp
  let I : Fin n₀ → DualInput MS B (extraTemplate s) N := fun t =>
    let q := enum t
    { e := fun _ => 1
      g := fun ω p z => by
        change Finset (Fin (s + 1)) at ω
        change Fin 0 → ℕ at p
        exact inputAt q ω p z
      e_bound := by intro p; norm_num
      g_bound := by
        intro ω p z
        change Finset (Fin (s + 1)) at ω
        change Fin 0 → ℕ at p
        have hν : 0 ≤ nu A N B z := pkgD_nu_nonneg A N B
          (fun i => harmonicNormalizer_pos (A.X N i) (primorial (N + 1))
            (primorial_pos _) (MS.gapStage.valid_raw_cutoffs N i)) z
        exact (hinputBound q ω p z).trans (by linarith) }
  have hIone (t : Fin n₀) (p : Fin (extraTemplate s).q → ℕ) : (I t).e p = 1 := rfl
  have hIbound (t : Fin n₀) (ω : Finset (Fin (extraTemplate s).d))
      (p : Fin (extraTemplate s).q → ℕ) (z : ℤ) : |(I t).g ω p z| ≤ 1 := by
    change Finset (Fin (s + 1)) at ω
    change Fin 0 → ℕ at p
    exact hinputBound (enum t) ω p z
  let L := (extraTemplate s).length (corrScales MS) l J0 N p0
  let U : Finset (Fin (s + 1) → Fin 2 → ℕ) :=
    Fintype.piFinset (fun _ : Fin (s + 1) =>
      Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  have hUmem (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
      (j : Fin (s + 1)) (b : Fin 2) : u j b < L := by
    have hu' : u ∈ Fintype.piFinset (fun _ : Fin (s + 1) =>
        Fintype.piFinset (fun _ : Fin 2 => Finset.range L)) := by simpa [U] using hu
    have huOuter := Fintype.mem_piFinset.mp hu'
    have huInner := Fintype.mem_piFinset.mp (huOuter j)
    exact Finset.mem_range.mp (huInner b)
  have hRecipeApprox : ∀ y : ℤ,
      ¬ InBoundaryStrip (A.H N l) ((s + 1) * A.H N l / J0) y →
      |Φ.eval N y - ∑ t, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y| ≤ δ := by
    intro y hy
    let width : ℕ := (s + 1) * A.H N l / J0
    let P := Pof y
    let k : ℤ := (y - y % (A.M N : ℤ)) / (A.M N : ℤ)
    let R := Recipes P.index (selected P)
    have hmargin : (width : ℤ) < y % (A.H N l : ℤ) ∧
        y % (A.H N l : ℤ) + (width : ℤ) < (A.H N l : ℤ) := by
      have h := hy
      simp only [InBoundaryStrip, not_or, not_le] at h
      exact h
    have hLformula : L = A.H N l / (J0 * A.M N) := by
      dsimp [L]
      change A.H N l / (J0 * directionModulus (corrScales MS) N
        (extraTemplate s).D p0) = _
      have hdir : directionModulus (corrScales MS) N (extraTemplate s).D p0 = A.M N := by
        simpa [CubeTemplate.modulus] using hmodulus N
      rw [hdir]
    have hdivBound : J0 * A.M N * L ≤ A.H N l := by
      rw [hLformula]
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.div_mul_le_self (A.H N l) (J0 * A.M N))
    have hRadius : (s + 1) * A.M N * L ≤ (s + 1) * A.H N l / J0 := by
      apply (Nat.le_div_iff_mul_le hJ0).2
      calc
        ((s + 1) * A.M N * L) * J0 = (s + 1) * (J0 * A.M N * L) := by ring
        _ ≤ (s + 1) * A.H N l := Nat.mul_le_mul_left (s + 1) hdivBound
    let v (u : Fin (s + 1) → Fin 2 → ℕ) : Fin (s + 1) → ℤ := fun j =>
      (u j 1 : ℤ) - u j 0
    have hshiftBound (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) :
        |(A.M N : ℤ) * ∑ j ∈ ω, v u j| ≤ (width : ℤ) := by
      have hvUpper (j : Fin (s + 1)) : v u j ≤ (L : ℤ) := by
        have h0 := hUmem u hu j 0
        have h1 := hUmem u hu j 1
        dsimp [v]
        omega
      have hvLower (j : Fin (s + 1)) : -(L : ℤ) ≤ v u j := by
        have h0 := hUmem u hu j 0
        have h1 := hUmem u hu j 1
        dsimp [v]
        omega
      have hcard : ω.card ≤ s + 1 := by
        calc
          ω.card ≤ (Finset.univ : Finset (Fin (s + 1))).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = s + 1 := by simp
      have hcardZ : (ω.card : ℤ) ≤ (s + 1 : ℤ) := by exact_mod_cast hcard
      have hLnonneg : 0 ≤ (L : ℤ) := by positivity
      have hsumUpper : ∑ j ∈ ω, v u j ≤ (s + 1 : ℤ) * (L : ℤ) := by
        calc
          ∑ j ∈ ω, v u j ≤ ∑ j ∈ ω, (L : ℤ) :=
            Finset.sum_le_sum fun j hj => hvUpper j
          _ = (ω.card : ℤ) * (L : ℤ) := by simp
          _ ≤ (s + 1 : ℤ) * (L : ℤ) :=
            mul_le_mul_of_nonneg_right hcardZ hLnonneg
      have hsumLower : -(s + 1 : ℤ) * (L : ℤ) ≤ ∑ j ∈ ω, v u j := by
        have hlow : (∑ j ∈ ω, -(L : ℤ)) ≤ ∑ j ∈ ω, v u j :=
          Finset.sum_le_sum (s := ω) (fun j hj => hvLower j)
        have hconst : ∑ j ∈ ω, -(L : ℤ) = -((ω.card : ℤ) * (L : ℤ)) := by simp
        have hlow' : -((ω.card : ℤ) * (L : ℤ)) ≤ ∑ j ∈ ω, v u j := by
          simpa [hconst] using hlow
        have hcardMul := mul_le_mul_of_nonneg_right hcardZ hLnonneg
        exact (neg_le_neg hcardMul).trans hlow'
      have hRadiusZ : (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) ≤ (width : ℤ) := by
        have hNat' : A.M N * (s + 1) * L ≤ width := by
          calc
            A.M N * (s + 1) * L = (s + 1) * A.M N * L := by ring
            _ ≤ width := hRadius
        exact_mod_cast hNat'
      have hMnonneg : 0 ≤ (A.M N : ℤ) := by positivity
      have hmulLower : -((A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ)) ≤
          (A.M N : ℤ) * ∑ j ∈ ω, v u j := by
        calc
          -((A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ)) =
              (A.M N : ℤ) * (-( (s + 1 : ℤ) * (L : ℤ))) := by ring
          _ ≤ (A.M N : ℤ) * ∑ j ∈ ω, v u j :=
            mul_le_mul_of_nonneg_left hsumLower hMnonneg
      have hmulUpper : (A.M N : ℤ) * ∑ j ∈ ω, v u j ≤
          (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) := by
        calc
          (A.M N : ℤ) * ∑ j ∈ ω, v u j ≤
              (A.M N : ℤ) * ((s + 1 : ℤ) * (L : ℤ)) :=
            mul_le_mul_of_nonneg_left hsumUpper hMnonneg
          _ = (A.M N : ℤ) * (s + 1 : ℤ) * (L : ℤ) := by ring
      apply abs_le.mpr
      exact ⟨(neg_le_neg hRadiusZ).trans hmulLower, hmulUpper.trans hRadiusZ⟩
    have hPshift (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) :
        Pof (y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) = P := by
      have hquot := ediv_stable_of_interior (A.H N l) width (A.Hpos N l) y
        ((A.M N : ℤ) * ∑ j ∈ ω, v u j) (hshiftBound u hu ω) hmargin.1 hmargin.2
      have hres := residue_and_progression_shift (A.M N) (A.Mpos N) y
        (∑ j ∈ ω, v u j)
      dsimp [P, Pof]
      rw [hquot, hres.1]
    have hcoord (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) :
        ((y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) -
          (y + (A.M N : ℤ) * ∑ j ∈ ω, v u j) % (A.M N : ℤ)) / (A.M N : ℤ) =
          k + ∑ j ∈ ω, v u j :=
      (residue_and_progression_shift (A.M N) (A.Mpos N) y
        (∑ j ∈ ω, v u j)).2
    let cube (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) : Fm.G P.index ⧸ Fm.Γ P.index :=
      P.g ^ (k + ∑ j ∈ ω, v u j) • P.x
    have hchart (u : Fin (s + 1) → Fin 2 → ℕ) :
        |R.eval Fm (cube u) - P.obs (P.g ^ k • P.x)| ≤ δ := by
      have h := hselected P P.g P.x k (v u)
      rw [abs_sub_comm] at h
      simpa only [R, cube, v] using h
    have hPhiRoot : Φ.eval N y = P.obs (P.g ^ k • P.x) := by
      simp [RepFamily.eval, OAI.SourceMenuLiteral.CosetPiece.eval, P, Pof, k, A]
    let faces : Finset (Finset (Fin (s + 1))) :=
      (Finset.univ : Finset (Finset (Fin (s + 1)))).erase ∅
    let shiftSum (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) : ℤ :=
      (∑ j ∈ ω, (u j 1 : ℤ)) - ∑ j ∈ ω, (u j 0 : ℤ)
    have hshiftSum (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) :
        shiftSum u ω = ∑ j ∈ ω, v u j := by
      dsimp [shiftSum, v]
      rw [← Finset.sum_sub_distrib]
    let zShift (u : Fin (s + 1) → Fin 2 → ℕ) (ω : Finset (Fin (s + 1))) : ℤ :=
      y + (A.M N : ℤ) * shiftSum u ω
    let shiftTerm (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ) : ℝ :=
      ∏ ω ∈ faces, (I (enum.symm q)).g ω p0
        (zShift u ω)
    have hmodEmpty :
        (extraTemplate s).modulus (corrScales MS) N (extraTemplateEmptyTuple s) = A.M N := by
      simpa [p0] using hmodulus N
    have hdual (q : RecipeIndex) :
      dualTest MS B (extraTemplate s) l J0 N (I (enum.symm q)) y =
          shiftAverage (Fin (s + 1)) L (shiftTerm q) := by
      rw [extraTemplate_dualTest_eq]
      rw [hmodEmpty]
      rw [show (extraTemplate s).length (corrScales MS) l J0 N
          (extraTemplateEmptyTuple s) = L by rfl]
      rw [(show (I (enum.symm q)).e (extraTemplateEmptyTuple s) = 1 by rfl), one_mul]
      change shiftAverage (Fin (s + 1)) L
          (fun u => ∏ ω ∈ faces,
            (I (enum.symm q)).g ω (extraTemplateEmptyTuple s)
              (y + (A.M N : ℤ) *
                ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) =
        shiftAverage (Fin (s + 1)) L (shiftTerm q)
      congr 1
      funext u
      simp [shiftTerm, faces, shiftSum, zShift, p0, extraTemplateEmptyTuple,
        emptyNatTuple, Finset.sum_sub_distrib]
    have hreindex :
        (∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y) =
          ∑ q : RecipeIndex, coeffQ q * dualTest MS B (extraTemplate s) l J0 N
            (I (enum.symm q)) y := by
      apply Fintype.sum_equiv enum
      intro t
      simp [coeff, coeffQ, I, enum.apply_symm_apply]
    have hsumAverage :
        (∑ q : RecipeIndex, coeffQ q * shiftAverage (Fin (s + 1)) L (shiftTerm q)) =
          shiftAverage (Fin (s + 1)) L
            (fun u => ∑ q : RecipeIndex, coeffQ q * shiftTerm q u) := by
      classical
      unfold shiftAverage
      let D : ℝ := ((L : ℝ) ^ (2 * Fintype.card (Fin (s + 1))))⁻¹
      calc
        _ = ∑ q : RecipeIndex, D *
              (coeffQ q * ∑ u ∈ U, shiftTerm q u) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = D * ∑ q : RecipeIndex, coeffQ q * ∑ u ∈ U, shiftTerm q u := by
          rw [← Finset.mul_sum]
        _ = D * ∑ u ∈ U, ∑ q : RecipeIndex, coeffQ q * shiftTerm q u := by
          congr 1
          change (∑ q ∈ (Finset.univ : Finset RecipeIndex),
              coeffQ q * ∑ u ∈ U, shiftTerm q u) =
            ∑ u ∈ U, ∑ q ∈ (Finset.univ : Finset RecipeIndex), coeffQ q * shiftTerm q u
          calc
            _ = ∑ q ∈ (Finset.univ : Finset RecipeIndex),
                  ∑ u ∈ U, coeffQ q * shiftTerm q u := by
                apply Finset.sum_congr rfl
                intro q hq
                rw [Finset.mul_sum]
            _ = _ := Finset.sum_comm
        _ = _ := by rfl
    have hPofShift (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (ω : Finset (Fin (s + 1))) : Pof (zShift u ω) = P := by
      have heq : zShift u ω = y + (A.M N : ℤ) * ∑ j ∈ ω, v u j := by
        simp [zShift, hshiftSum]
      rw [heq]
      exact hPshift u hu ω
    have hcoordShift (u : Fin (s + 1) → Fin 2 → ℕ)
        (ω : Finset (Fin (s + 1))) :
        (zShift u ω - zShift u ω % (A.M N : ℤ)) / (A.M N : ℤ) =
          k + shiftSum u ω := by
      have h := hcoord u ω
      simpa [zShift, hshiftSum] using h
    have hinputShift (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (ω : Finset (Fin (s + 1))) :
        inputAt q ω p0 (zShift u ω) =
          if hi : q.1 = P.index then
            if hn : q.2.2.val < R.terms then
              if hω : ω = rootFace then
                R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω) * scaleFor P q.2.2.val hn
              else R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω)
            else 0
          else 0 := by
      dsimp [inputAt]
      rw [hPofShift u hu ω, hcoordShift u ω]
      simp [R, cube, hshiftSum u ω]
    have hIinput (q : RecipeIndex) (ω : Finset (Fin (s + 1))) (z : ℤ) :
        (I (enum.symm q)).g ω p0 z = inputAt q ω p0 z := by
      change inputAt (enum (enum.symm q)) ω p0 z = inputAt q ω p0 z
      rw [enum.apply_symm_apply]
    have hprodActive (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 = P.index)
        (hn : q.2.2.val < R.terms) :
        shiftTerm q u = scaleFor P q.2.2.val hn *
          ∏ ω ∈ faces, R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω) := by
      let f : Finset (Fin (s + 1)) → ℝ := fun ω =>
        R.factor ⟨q.2.2.val, hn⟩ ω (cube u ω)
      let g : Finset (Fin (s + 1)) → ℝ := fun ω =>
        if ω = rootFace then f ω * scaleFor P q.2.2.val hn else f ω
      have hfactor (ω : Finset (Fin (s + 1))) (hω : ω ∈ faces) :
          inputAt q ω p0 (zShift u ω) = g ω := by
        have h := hinputShift q u hu ω
        simpa [hi, hn, R, cube, f, g] using h
      calc
        shiftTerm q u = ∏ ω ∈ faces, g ω := by
          dsimp [shiftTerm]
          apply Finset.prod_congr rfl
          intro ω hω
          rw [hIinput q ω (zShift u ω)]
          exact hfactor ω hω
        _ = scaleFor P q.2.2.val hn * ∏ ω ∈ faces, f ω := by
          calc
            ∏ ω ∈ faces, g ω =
                (∏ ω ∈ faces.erase rootFace, g ω) * g rootFace :=
              (Finset.prod_erase_mul faces g hrootFace).symm
            _ = (∏ ω ∈ faces.erase rootFace, f ω) *
                  (f rootFace * scaleFor P q.2.2.val hn) := by
              congr 1
              · apply Finset.prod_congr rfl
                intro ω hω
                have hne : ω ≠ rootFace := (Finset.mem_erase.mp hω).1
                simp [g, hne]
              all_goals simp [g]
            _ = scaleFor P q.2.2.val hn *
                  ((∏ ω ∈ faces.erase rootFace, f ω) * f rootFace) := by ring
            _ = scaleFor P q.2.2.val hn * ∏ ω ∈ faces, f ω := by
              rw [Finset.prod_erase_mul faces f hrootFace]
    have hprodZeroIndex (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 ≠ P.index) : shiftTerm q u = 0 := by
      have hz : inputAt q rootFace p0 (zShift u rootFace) = 0 := by
        have h := hinputShift q u hu rootFace
        simpa [hi] using h
      change (∏ ω ∈ faces, (I (enum.symm q)).g ω p0 (zShift u ω)) = 0
      apply Finset.prod_eq_zero hrootFace
      rw [hIinput q rootFace (zShift u rootFace)]
      exact hz
    have hprodZeroTerm (q : RecipeIndex) (u : Fin (s + 1) → Fin 2 → ℕ)
        (hu : u ∈ U) (hi : q.1 = P.index)
        (hn : ¬ q.2.2.val < R.terms) : shiftTerm q u = 0 := by
      have hz : inputAt q rootFace p0 (zShift u rootFace) = 0 := by
        have h := hinputShift q u hu rootFace
        simpa [hi, hn, R] using h
      change (∏ ω ∈ faces, (I (enum.symm q)).g ω p0 (zShift u ω)) = 0
      apply Finset.prod_eq_zero hrootFace
      rw [hIinput q rootFace (zShift u rootFace)]
      exact hz
    have htermSummand (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U)
        (i : Fin Fm.size) (j : Fin (m i)) (n : Fin nTerms) :
        coeffQ ⟨i, ⟨j, n⟩⟩ * shiftTerm ⟨i, ⟨j, n⟩⟩ u =
          if hi : i = P.index then
            if hn : n.val < R.terms then
              coeffQ ⟨i, ⟨j, n⟩⟩ *
                (scaleFor P n.val hn *
                  ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω))
            else 0
          else 0 := by
      by_cases hi : i = P.index
      · subst i
        by_cases hn : n.val < R.terms
        · have h := hprodActive ⟨P.index, ⟨j, n⟩⟩ u hu rfl hn
          simp [h, hn]
        · have h := hprodZeroTerm ⟨P.index, ⟨j, n⟩⟩ u hu rfl hn
          simp [h, hn]
      · have h := hprodZeroIndex ⟨i, ⟨j, n⟩⟩ u hu hi
        simp [h, hi]
    have hinner (u : Fin (s + 1) → Fin 2 → ℕ) (hu : u ∈ U) :
        (∑ q : RecipeIndex, coeffQ q * shiftTerm q u) = R.eval Fm (cube u) := by
      classical
      change (∑ q : (Σ i : Fin Fm.size, Σ j : Fin (m i), Fin nTerms),
        coeffQ q * shiftTerm q u) = R.eval Fm (cube u)
      simp only [Fintype.sum_sigma]
      change (∑ i : Fin Fm.size, ∑ j : Fin (m i), ∑ n : Fin nTerms,
        coeffQ ⟨i, ⟨j, n⟩⟩ * shiftTerm ⟨i, ⟨j, n⟩⟩ u) = R.eval Fm (cube u)
      simp_rw [htermSummand u hu]
      simp [Finset.sum_ite_eq']
      have hmassSum (n : Fin nTerms) :
          (∑ j : Fin (m P.index), coeffQ ⟨P.index, ⟨j, n⟩⟩) =
            coeffMass P.index n.val := by
        simp [coeffQ, coeffMass]
      have hscaled (n : Fin nTerms) (hn : n.val < R.terms) :
          coeffMass P.index n.val * scaleFor P n.val hn = R.coeff ⟨n.val, hn⟩ := by
        by_cases hz : coeffMass P.index n.val = 0
        · have hcoef : R.coeff ⟨n.val, hn⟩ = 0 := by
            have hle := hcoeffLeMass P n.val (by simpa [R] using hn)
            have habs : |R.coeff ⟨n.val, hn⟩| = 0 := by
              apply le_antisymm
              · have hle' : |R.coeff ⟨n.val, hn⟩| ≤ coeffMass P.index n.val := by
                  simpa [R] using hle
                simpa [hz] using hle'
              · exact abs_nonneg _
            exact abs_eq_zero.mp habs
          simp [scaleFor, hz, hcoef]
        · have hscale : scaleFor P n.val hn =
              R.coeff ⟨n.val, hn⟩ / coeffMass P.index n.val := by
            simp [scaleFor, hz, R]
          rw [hscale]
          field_simp [hz]
      have htermsBound : R.terms ≤ nTerms := by
        have hj : (Recipes P.index (selected P)).terms ≤
            ∑ j : Fin (m P.index), (Recipes P.index j).terms := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun j : Fin (m P.index) => (Recipes P.index j).terms)
            (fun j hj => Nat.zero_le _)
            (Finset.mem_univ (selected P))
        have hi : (∑ j : Fin (m P.index), (Recipes P.index j).terms) ≤
            ∑ i : Fin Fm.size, ∑ j : Fin (m i), (Recipes i j).terms := by
          exact Finset.single_le_sum
            (s := Finset.univ)
            (f := fun i : Fin Fm.size => ∑ j : Fin (m i), (Recipes i j).terms)
            (fun i hi => Finset.sum_nonneg fun j hj => Nat.zero_le _)
            (Finset.mem_univ P.index)
        simpa [R, nTerms] using hj.trans hi
      let paddedTerm (n : ℕ) : ℝ :=
        if hn : n < R.terms then
          R.coeff ⟨n, hn⟩ * ∏ ω ∈ faces, R.factor ⟨n, hn⟩ ω (cube u ω)
        else 0
      have hpad : (∑ n : Fin nTerms, paddedTerm n.val) =
          (∑ n : Fin R.terms, paddedTerm n.val) := by
        rw [Fin.sum_univ_eq_sum_range paddedTerm nTerms,
          Fin.sum_univ_eq_sum_range paddedTerm R.terms]
        apply (Finset.sum_subset (Finset.range_mono htermsBound) ?_).symm
        intro n hn hnot
        have hnot' : ¬ n < R.terms := by
          intro hlt
          exact hnot (Finset.mem_range.mpr hlt)
        simp [paddedTerm, hnot']
      rw [Finset.sum_comm]
      calc
        _ = ∑ n : Fin nTerms,
              if hn : n.val < R.terms then
                coeffMass P.index n.val *
                  (scaleFor P n.val hn *
                    ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω))
              else 0 := by
          apply Finset.sum_congr rfl
          intro n hnmem
          by_cases hn : n.val < R.terms
          · simp [hn]
            rw [← Finset.sum_mul, hmassSum n]
          · simp [hn]
        _ = ∑ n : Fin nTerms,
              if hn : n.val < R.terms then
                R.coeff ⟨n.val, hn⟩ *
                  ∏ ω ∈ faces, R.factor ⟨n.val, hn⟩ ω (cube u ω)
              else 0 := by
          apply Finset.sum_congr rfl
          intro n hnmem
          by_cases hn : n.val < R.terms
          · simp [hn]
            rw [← mul_assoc, hscaled n hn]
          · simp [hn]
        _ = R.eval Fm (cube u) := by
          simpa [paddedTerm, Charted.CornerRecipe.eval, faces] using hpad
    have hSumReconstruct :
        (∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J0 N (I t) y) =
          shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) := by
      calc
        _ = ∑ q : RecipeIndex, coeffQ q * dualTest MS B (extraTemplate s) l J0 N
              (I (enum.symm q)) y := hreindex
        _ = ∑ q : RecipeIndex, coeffQ q * shiftAverage (Fin (s + 1)) L (shiftTerm q) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hdual q]
        _ = shiftAverage (Fin (s + 1)) L
              (fun u => ∑ q : RecipeIndex, coeffQ q * shiftTerm q u) := hsumAverage
        _ = shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) := by
          unfold shiftAverage
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          exact hinner u hu
    have hAvg : |shiftAverage (Fin (s + 1)) L (fun u => R.eval Fm (cube u)) -
        P.obs (P.g ^ k • P.x)| ≤ δ := by
      exact shiftAverage_sub_const_abs_le (d := s + 1) (L := L)
        (by omega) (by simpa [L] using hlength)
        (fun u => R.eval Fm (cube u)) (P.obs (P.g ^ k • P.x)) δ hchart
    rw [hPhiRoot, hSumReconstruct]
    simpa [abs_sub_comm] using hAvg
  refine ⟨I, ?_, ?_, hRecipeApprox⟩
  · intro t p
    exact hIone t p
  · intro t ω p z
    exact hIbound t ω p z

/-- (eq:prediction-weighted-boundary), 05:325–342: the boundary strips of relative length
`(s+1)/J₀` carry `(1 + ν_B)μ_i`-mass `O_s(J₀^{-1}) + o(1)`.  The constant depends on `s` only. -/
theorem weighted_boundary (s : ℕ) :
    ∃ C : ℝ, ∀ {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
      (MS : MasterScales K As sl Dm) (B : Block K) (l : Fin K), ValidGap B l →
      ∀ J0 : ℕ, 0 < J0 → ∀ ε > 0, ∀ᶠ N in atTop,
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J0) y) ≤ C / J0 + ε := by
  obtain ⟨C, hC⟩ := weighted_boundary_aux s
  refine ⟨C, ?_⟩
  intro K sl As Dm MS B l hl J0 hJ0 ε hε
  have h := hC MS B l hl J0 hJ0 ε hε
  filter_upwards [h] with N hN
  simpa [boundaryIndicator, InBoundaryStrip, pkgDBoundaryIndicator,
    pkgDBoundaryStrip] using hN

/-- Lemma `lem:nilsequence-testing` (eq:prediction-nilsequence-testing), 05:275–285, 344–353:
for a dense model `F`, a block `B`, a valid gap `l`, and a fixed menu of step `≤ s` with a fixed
Lipschitz bound, `E_{μ_i}(ρ − F) S' = o(1)` uniformly over the representing families `S'` at gap
`l` (bounded real families follow by affine combination with the constant family).  `1 ∈ Dm`
makes the extra type `extraTemplate s` allowed, so that `IsDenseModel` covers it. -/
theorem nilsequence_testing (MS : MasterScales K As sl Dm) (h1 : (1 : IntegerPolynomial sl) ∈ Dm)
    (χ : ℕ → Fin r) (F : BlockFamily K r) (hF : IsDenseModel MS χ F) (B : Block K) (a : ℚ) (ha : a ∈ As) (c : Fin r) (l : Fin K)
    (hl : ValidGap B l) {s : ℕ} (Fm : Menu s) (Km : ℝ≥0) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ Φ : RepFamily MS.core.parameters l Fm Km,
      |Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y)| ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n₀, coeff, hrecipes⟩ :=
    nilsequence_recipe_tests MS B l hl Fm Km δ hδ
  let C₀ : ℝ := ∑ t : Fin n₀, |coeff t|
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact Finset.sum_nonneg fun t _ => abs_nonneg _
  obtain ⟨Cbd, hboundary⟩ := weighted_boundary s
  let CbdPlus : ℝ := max Cbd 0
  let ηb : ℝ := ε / (16 * (1 + C₀))
  let ηm : ℝ := ε / (8 * (1 + C₀))
  have hηb : 0 < ηb := by dsimp [ηb]; positivity
  have hηm : 0 < ηm := by dsimp [ηm]; positivity
  have hthreshold : 0 ≤ 16 * (1 + C₀) * CbdPlus / ε := by positivity
  obtain ⟨J₀, hJ₀gt⟩ := exists_nat_gt (16 * (1 + C₀) * CbdPlus / ε)
  have hJ₀ : 0 < J₀ := by
    have hJ₀real : 0 < (J₀ : ℝ) := lt_of_le_of_lt hthreshold hJ₀gt
    exact_mod_cast hJ₀real
  have hCbdPlus : Cbd ≤ CbdPlus := le_max_left _ _
  have hCbdDiv : Cbd / (J₀ : ℝ) ≤ ε / (16 * (1 + C₀)) := by
    have hprod : 16 * (1 + C₀) * CbdPlus < ε * (J₀ : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hJ₀gt
    have hprod' : Cbd * (16 * (1 + C₀)) ≤ ε * (J₀ : ℝ) := by
      calc
        Cbd * (16 * (1 + C₀)) ≤ CbdPlus * (16 * (1 + C₀)) :=
          mul_le_mul_of_nonneg_right hCbdPlus (by positivity)
        _ = 16 * (1 + C₀) * CbdPlus := by ring
        _ ≤ ε * (J₀ : ℝ) := le_of_lt hprod
    rw [div_le_div_iff₀ (by positivity : 0 < (J₀ : ℝ)) (by positivity)]
    exact hprod'
  have hboundaryN := hboundary MS B l hl J₀ hJ₀ ηb hηb
  have hboundarySmall : Cbd / (J₀ : ℝ) + ηb ≤ ε / (8 * (1 + C₀)) := by
    rw [show ηb = ε / (16 * (1 + C₀)) by rfl]
    calc
      Cbd / (J₀ : ℝ) + ε / (16 * (1 + C₀)) ≤
          ε / (16 * (1 + C₀)) + ε / (16 * (1 + C₀)) :=
        add_le_add_left hCbdDiv _
      _ = ε / (8 * (1 + C₀)) := by field_simp; norm_num
  have hrecipesN := hrecipes J₀ hJ₀
  have hmeanN := pivotEmu_one_plus_nu_le_three MS B l hl
  have hnuN := pivotNu_nonneg_eventually MS B
  have hAllowed : Allowed Dm (extraTemplate s) :=
    extraTemplate_allowed (K := K) (sl := sl) (s := s) (As := As) (Dm := Dm) h1
  have hDenseN := hF.2 B a ha c l hl (extraTemplate s) hAllowed J₀ hJ₀ ηm hηm
  filter_upwards [hrecipesN, hboundaryN, hmeanN, hnuN, hDenseN]
    with N hrecipesN hboundaryN hmeanN hnuN hDenseN
  intro Φ
  obtain ⟨I, hIone, hIbound, happrox⟩ := hrecipesN Φ
  have hD : ∀ t y, |dualTest MS B (extraTemplate s) l J₀ N (I t) y| ≤ 1 := by
    intro t y
    exact extraDualTest_abs_le_one (MS := MS) (B := B) (s := s) (l := l)
      (J0 := J₀) (N := N) (I := I t)
      (fun p => hIone t p) (fun ω p z => hIbound t ω p z) y
  let Q : ℤ → ℝ := fun y =>
    ∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y
  have hQ : ∀ y, |Q y| ≤ C₀ := by
    intro y
    dsimp [Q, C₀]
    calc
      |∑ t : Fin n₀, coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y|
          ≤ ∑ t : Fin n₀, |coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y| :=
            by
              simpa [Real.norm_eq_abs] using
                (norm_sum_le (Finset.univ : Finset (Fin n₀))
                  (fun t => coeff t * dualTest MS B (extraTemplate s) l J₀ N (I t) y))
      _ ≤ ∑ t : Fin n₀, |coeff t| := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hD t y)
  have hPhi : ∀ y, Φ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    dsimp [RepFamily.eval, OAI.SourceMenuLiteral.CosetPiece.eval]
    exact (Φ.piece N (y / (MS.core.parameters.H N l : ℤ))
      (y % (MS.core.parameters.M N : ℤ))).range _
  have hdiff : ∀ y,
      |Φ.eval N y - Q y| ≤ δ + (1 + C₀) *
        boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y := by
    intro y
    by_cases hs : InBoundaryStrip (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y
    · have hb : boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y = 1 := by
        simp [boundaryIndicator, hs]
      rw [hb]
      have hphi0 := (hPhi y).1
      have hphi1 := (hPhi y).2
      calc
        |Φ.eval N y - Q y| ≤ |Φ.eval N y| + |Q y| := by
          calc
            |Φ.eval N y - Q y| = |Φ.eval N y + -Q y| := by congr 1 <;> ring
            _ ≤ |Φ.eval N y| + |-Q y| := abs_add_le _ _
            _ = |Φ.eval N y| + |Q y| := by rw [abs_neg]
        _ ≤ 1 + C₀ := by
          have hpa : |Φ.eval N y| ≤ 1 := abs_le.mpr ⟨by linarith, hphi1⟩
          exact add_le_add hpa (hQ y)
        _ ≤ δ + (1 + C₀) := by
          calc
            1 + C₀ = 0 + (1 + C₀) := by simp
            _ ≤ δ + (1 + C₀) := add_le_add_left hδ.le _
        _ = δ + (1 + C₀) * 1 := by simp
    · have hb : boundaryIndicator (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y = 0 := by
        simp [boundaryIndicator, hs]
      rw [hb]
      simpa [Q] using happrox y hs
  have hcolor0 (y : ℤ) : 0 ≤ colorFactor MS.core.parameters χ N B a c y :=
    rationalColorIndicator_nonneg χ c _
  have hcolor1 (y : ℤ) : colorFactor MS.core.parameters χ N B a c y ≤ 1 := by
    classical
    unfold colorFactor rationalColorIndicator
    split_ifs <;> norm_num
  have hrhoF : ∀ y, |rho MS.core.parameters χ N B a c y - F N B a c y| ≤
      1 + nu MS.core.parameters N B y := by
    intro y
    have hν := hnuN y
    have hFval := hF.1 N B a c y
    have hρ0 : 0 ≤ rho MS.core.parameters χ N B a c y := by
      simp [rho]
      exact mul_nonneg hν (hcolor0 y)
    have hρν : rho MS.core.parameters χ N B a c y ≤ nu MS.core.parameters N B y := by
      simp [rho]
      exact mul_le_of_le_one_right hν (hcolor1 y)
    rcases hFval with ⟨hF0, hF1⟩
    apply abs_le.mpr
    constructor <;> simp only [rho] at * <;> nlinarith
  have herrorPoint (y : ℤ) :
      |(rho MS.core.parameters χ N B a c y - F N B a c y) *
          (Φ.eval N y - Q y)| ≤
        (1 + nu MS.core.parameters N B y) *
          (δ + (1 + C₀) * boundaryIndicator
            (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) := by
    have hweight : 0 ≤ 1 + nu MS.core.parameters N B y := by linarith [hnuN y]
    have hsmall : 0 ≤ δ + (1 + C₀) * boundaryIndicator
        (MS.core.parameters.H N l) ((s + 1) * MS.core.parameters.H N l / J₀) y := by
      by_cases hs : InBoundaryStrip (MS.core.parameters.H N l)
          ((s + 1) * MS.core.parameters.H N l / J₀) y
      · simp [boundaryIndicator, hs]
        positivity
      · simp [boundaryIndicator, hs]
        positivity
    rw [abs_mul]
    exact mul_le_mul (hrhoF y) (hdiff y) (abs_nonneg _) hweight
  have herror := Emu_abs_bound_by_weight MS.core.parameters N B.1
    (fun y => (rho MS.core.parameters χ N B a c y - F N B a c y) *
      (Φ.eval N y - Q y))
    (fun y => (1 + nu MS.core.parameters N B y) *
      (δ + (1 + C₀) * boundaryIndicator (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y))
    (fun y => harmonicLaw_nonneg_of_Xpos
      (MS.core.parameters.X N B.1) (primorial (N + 1))
      (MS.core.parameters.Xpos N B.1) y)
    herrorPoint
  have herrorValue : |Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * (Φ.eval N y - Q y))| ≤
      δ * Emu MS.core.parameters N B.1 (fun y => 1 + nu MS.core.parameters N B y) +
        (1 + C₀) * Emu MS.core.parameters N B.1 (fun y =>
          (1 + nu MS.core.parameters N B y) * boundaryIndicator
            (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) := by
    have hlin := Emu_const_add_mul MS.core.parameters N B.1
      (fun y => 1 + nu MS.core.parameters N B y)
      (fun y => boundaryIndicator (MS.core.parameters.H N l)
        ((s + 1) * MS.core.parameters.H N l / J₀) y) δ (1 + C₀)
    calc
      _ ≤ Emu MS.core.parameters N B.1 (fun y =>
          (1 + nu MS.core.parameters N B y) *
            (δ + (1 + C₀) * boundaryIndicator (MS.core.parameters.H N l)
              ((s + 1) * MS.core.parameters.H N l / J₀) y)) := herror
      _ = _ := hlin
  have hpairing : |Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y)| ≤ C₀ * ηm := by
    rw [Emu_sum_pairing MS.core.parameters N B.1
      (fun y => rho MS.core.parameters χ N B a c y - F N B a c y) coeff
      (fun t y => dualTest MS B (extraTemplate s) l J₀ N (I t) y)]
    have hdense (t : Fin n₀) := hDenseN (I t)
    calc
      |∑ t : Fin n₀, coeff t * Emu MS.core.parameters N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) *
            dualTest MS B (extraTemplate s) l J₀ N (I t) y)|
          ≤ ∑ t : Fin n₀, |coeff t * Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              dualTest MS B (extraTemplate s) l J₀ N (I t) y)| := by
            simpa [Real.norm_eq_abs] using
              (norm_sum_le (Finset.univ : Finset (Fin n₀))
                (fun t => coeff t * Emu MS.core.parameters N B.1 (fun y =>
                  (rho MS.core.parameters χ N B a c y - F N B a c y) *
                    dualTest MS B (extraTemplate s) l J₀ N (I t) y)))
      _ ≤ ∑ t : Fin n₀, |coeff t| * ηm := by
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hdense t) (abs_nonneg _)
      _ = C₀ * ηm := by rw [← Finset.sum_mul]
  have hsplit : Emu MS.core.parameters N B.1 (fun y =>
      (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y) =
      Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y) +
      Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) *
          (Φ.eval N y - Q y)) := by
    calc
      _ = Emu MS.core.parameters N B.1 (fun y =>
          (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y +
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              (Φ.eval N y - Q y)) := by
        congr 1
        funext y
        ring
      _ = _ := pkgD_Emu_add MS.core.parameters N B.1 _ _
  have hbdSmall : (1 + C₀) * (Cbd / (J₀ : ℝ) + ηb) ≤ ε / 8 := by
    rw [show ηb = ε / (16 * (1 + C₀)) by rfl]
    have h := mul_le_mul_of_nonneg_left hboundarySmall (by positivity : (0 : ℝ) ≤ 1 + C₀)
    calc
      _ ≤ (1 + C₀) * (ε / (8 * (1 + C₀))) := h
      _ = ε / 8 := by field_simp
  have hpairSmall : C₀ * ηm ≤ ε / 8 := by
    rw [show ηm = ε / (8 * (1 + C₀)) by rfl]
    have hC0bound : C₀ ≤ 1 + C₀ := by linarith [hC₀]
    have hmul := mul_le_mul_of_nonneg_right hC0bound (by positivity : (0 : ℝ) ≤ ε / (8 * (1 + C₀)))
    have hden : (1 + C₀) * (ε / (8 * (1 + C₀))) = ε / 8 := by field_simp
    nlinarith
  have herrorSmall : δ * Emu MS.core.parameters N B.1 (fun y =>
      1 + nu MS.core.parameters N B y) + (1 + C₀) *
        Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
          boundaryIndicator (MS.core.parameters.H N l)
            ((s + 1) * MS.core.parameters.H N l / J₀) y) ≤ 7 * ε / 16 := by
    have hbd := hboundaryN
    have hmean := hmeanN
    have hmean' := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ δ)
    have hbd' := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ 1 + C₀)
    have hmeanBound : δ * Emu MS.core.parameters N B.1
        (fun y => 1 + nu MS.core.parameters N B y) ≤ 3 * ε / 16 := by
      calc
        δ * Emu MS.core.parameters N B.1 (fun y => 1 + nu MS.core.parameters N B y) ≤ δ * 3 := hmean'
        _ = 3 * ε / 16 := by rw [show δ = ε / 16 by rfl]; ring
    calc
      _ ≤ 3 * ε / 16 + ε / 8 :=
        add_le_add hmeanBound (hbd'.trans hbdSmall)
      _ ≤ 7 * ε / 16 := by nlinarith [hε]
  calc
    |Emu MS.core.parameters N B.1 (fun y =>
        (rho MS.core.parameters χ N B a c y - F N B a c y) * Φ.eval N y)|
        ≤ |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) * Q y)| +
          |Emu MS.core.parameters N B.1 (fun y =>
            (rho MS.core.parameters χ N B a c y - F N B a c y) *
              (Φ.eval N y - Q y))| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ C₀ * ηm + (δ * Emu MS.core.parameters N B.1 (fun y =>
          1 + nu MS.core.parameters N B y) + (1 + C₀) *
            Emu MS.core.parameters N B.1 (fun y => (1 + nu MS.core.parameters N B y) *
              boundaryIndicator (MS.core.parameters.H N l)
                ((s + 1) * MS.core.parameters.H N l / J₀) y)) := by
      exact add_le_add hpairing herrorValue
    _ ≤ ε / 8 + 7 * ε / 16 := add_le_add hpairSmall herrorSmall
    _ ≤ ε := by nlinarith [hε]

end

end HindmanSumsProducts.Prediction
