import HindmanSumsProducts.Prediction.Results
import HindmanSumsProducts.ChainSelection.FiniteRamsey
import OAI.Combinatorics.SumProduct.Alignment.HarmonicTranslation01

/-! Helper lemmas for §5 (part S5-F). -/

open Filter
open scoped BigOperators NNReal Topology

namespace HindmanSumsProducts.Prediction

noncomputable section

/-- A bounded real sequence has its stated ultrafilter limit as a limit along the ultrafilter. -/
lemma ulim_tendsto_of_abs_le (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ N, |f N| ≤ C) : Tendsto f (U : Filter ℕ) (𝓝 (ulim U f)) := by
  let I := {x : ℝ // x ∈ Set.Icc (-C) C}
  let g : ℕ → I := fun N => ⟨f N, abs_le.mp (hf N)⟩
  letI : CompactSpace I :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (-C) C))
  have hg : Tendsto g (U : Filter ℕ) (𝓝 ((U.map g).lim)) := by
    change Filter.map g (U : Filter ℕ) ≤ 𝓝 ((U.map g).lim)
    exact Ultrafilter.le_nhds_lim (U.map g)
  have hv : Tendsto f (U : Filter ℕ) (𝓝 (((U.map g).lim : I) : ℝ)) := by
    have hc : Tendsto (fun N => (g N).val) (U : Filter ℕ)
        (𝓝 (((U.map g).lim : I) : ℝ)) := by
      exact (continuous_subtype_val.tendsto ((U.map g).lim)).comp hg
    simpa only [g] using hc
  have heq : ulim U f = (((U.map g).lim : I) : ℝ) := by
    change limUnder (U : Filter ℕ) f = _
    exact hv.limUnder_eq
  rw [heq]
  exact hv

lemma ulim_add_of_abs_le (U : Ultrafilter ℕ) (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ N, |f N| ≤ Cf) (hg : ∀ N, |g N| ≤ Cg) :
    ulim U (fun N => f N + g N) = ulim U f + ulim U g := by
  have h := (ulim_tendsto_of_abs_le U f Cf hf).add (ulim_tendsto_of_abs_le U g Cg hg)
  simpa [ulim] using h.limUnder_eq

lemma ulim_mul_of_abs_le (U : Ultrafilter ℕ) (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ N, |f N| ≤ Cf) (hg : ∀ N, |g N| ≤ Cg) :
    ulim U (fun N => f N * g N) = ulim U f * ulim U g := by
  have h := (ulim_tendsto_of_abs_le U f Cf hf).mul (ulim_tendsto_of_abs_le U g Cg hg)
  simpa [ulim] using h.limUnder_eq

lemma ulim_nonneg_of_forall (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ N, |f N| ≤ C) (hn : ∀ N, 0 ≤ f N) : 0 ≤ ulim U f := by
  have hlim := ulim_tendsto_of_abs_le U f C hf
  have h := isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall hn)
  exact h

private lemma harmonicNormalizer_eq_translationMass (X W : ℕ) :
    harmonicNormalizer X W =
      OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) := by
  classical
  have hIco : Finset.Ico (X : ℤ) ((X ^ 2 : ℕ) : ℤ) =
      (Finset.Ico X (X ^ 2)).image (fun n : ℕ => (n : ℤ)) := by
    ext z
    simp only [Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨hzlo, hzhi⟩
      have hz0 : (0 : ℤ) ≤ z := le_trans (by exact_mod_cast (Nat.zero_le X)) hzlo
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
      have hnlo : X ≤ z.toNat := by
        rw [← hzcast] at hzlo
        exact_mod_cast hzlo
      have hnhi : z.toNat < X ^ 2 := by
        rw [← hzcast] at hzhi
        exact_mod_cast hzhi
      exact ⟨z.toNat, ⟨hnlo, hnhi⟩, hzcast⟩
    · rintro ⟨n, ⟨hnlo, hnhi⟩, rfl⟩
      exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
  have hsub : (OAI.HarmonicTranslation.raw X W).support ⊆
      Finset.Ico (X : ℤ) ((X ^ 2 : ℕ) : ℤ) := by
    unfold OAI.HarmonicTranslation.raw
    exact Finsupp.support_onFinset_subset
  have hmass : OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) =
      ∑ z ∈ Finset.Ico (X : ℤ) ((X ^ 2 : ℕ) : ℤ),
        OAI.HarmonicTranslation.raw X W z := by
    rw [OAI.HarmonicTranslation.mass]
    exact (OAI.HarmonicTranslation.raw X W).sum_of_support_subset hsub (fun _ a => a) (by simp)
  rw [hmass, hIco]
  rw [Finset.sum_image (fun a ha b hb hab => Int.natCast_inj.mp hab)]
  unfold harmonicNormalizer
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [OAI.HarmonicTranslation.raw_apply]
  rcases Finset.mem_Ico.mp hn with ⟨hnlo, hnhi⟩
  by_cases hcop : Nat.Coprime n W
  · have hnloZ : (X : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnlo
    have hnhiZ : (n : ℤ) < ((X ^ 2 : ℕ) : ℤ) := by exact_mod_cast hnhi
    have hcopZ : IsCoprime (n : ℤ) (W : ℤ) := hcop.cast
    rw [if_pos hcop]
    have hcond : (X : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < (X : ℤ) ^ 2 ∧
        IsCoprime (n : ℤ) (W : ℤ) :=
      ⟨hnloZ, by simpa only [Nat.cast_pow] using hnhiZ, hcopZ⟩
    rw [if_pos hcond]
    simp [one_div]
  · simp [hcop, Int.isCoprime_iff_nat_coprime]

private lemma harmonicLaw_eq_translationLaw (X W : ℕ) (hX : 0 < X) (z : ℤ) :
    harmonicLaw X W z = (OAI.HarmonicTranslation.law X W) z := by
  rw [OAI.HarmonicTranslation.law]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [harmonicLaw, OAI.HarmonicTranslation.raw_apply]
  rw [harmonicNormalizer_eq_translationMass]
  by_cases hz : 0 ≤ z
  · have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
    have hzabs : z.natAbs = z.toNat := by
      have hh : (z.natAbs : ℤ) = (z.toNat : ℤ) := by
        rw [Int.natAbs_of_nonneg hz, hzcast]
      exact_mod_cast hh
    have hcop : IsCoprime z (W : ℤ) ↔ Nat.Coprime z.toNat W := by
      rw [Int.isCoprime_iff_nat_coprime]
      simp [hzabs]
    have hcond :
        (0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) ↔
          (X : ℤ) ≤ z ∧ z < (X : ℤ) ^ 2 ∧ IsCoprime z (W : ℤ) := by
      constructor
      · rintro ⟨_, hlo, hhi, hcopNat⟩
        have hloZ : (X : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hlo
        have hhiZ : (z.toNat : ℤ) < (X : ℤ) ^ 2 := by exact_mod_cast hhi
        exact ⟨by simpa only [hzcast] using hloZ,
          by simpa only [hzcast] using hhiZ, hcop.mpr hcopNat⟩
      · rintro ⟨hloZ, hhiZ, hcopZ⟩
        have hlo : X ≤ z.toNat := by
          have h : (X : ℤ) ≤ (z.toNat : ℤ) := by simpa only [hzcast] using hloZ
          exact_mod_cast h
        have hhi : z.toNat < X ^ 2 := by
          have h : (z.toNat : ℤ) < (X : ℤ) ^ 2 := by
            simpa only [hzcast] using hhiZ
          exact_mod_cast h
        exact ⟨hz, hlo, hhi, hcop.mp hcopZ⟩
    by_cases hraw : (X : ℤ) ≤ z ∧ z < (X : ℤ) ^ 2 ∧ IsCoprime z (W : ℤ)
    · have hlocal := hcond.mpr hraw
      rw [if_pos hlocal, if_pos hraw]
      rw [show (z.toNat : ℝ) = (z : ℝ) by exact_mod_cast hzcast]
      by_cases hmass : OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) = 0
      · simp [hmass]
      · have hmassNonneg : 0 ≤ OAI.HarmonicTranslation.mass
            (OAI.HarmonicTranslation.raw X W) :=
          OAI.HarmonicTranslation.mass_nonneg _ (fun y => OAI.HarmonicTranslation.raw_nonneg hX y)
        have hmassPos : 0 < OAI.HarmonicTranslation.mass
            (OAI.HarmonicTranslation.raw X W) := lt_of_le_of_ne hmassNonneg (Ne.symm hmass)
        have hzpos : 0 < z.toNat := by
          exact lt_of_lt_of_le hX hlocal.2.1
        have hzposR : (0 : ℝ) < (z.toNat : ℝ) := by exact_mod_cast hzpos
        field_simp [ne_of_gt hmassPos, ne_of_gt hzposR] <;> ring
    · have hlocal : ¬ (0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) :=
        fun h => hraw (hcond.mp h)
      simp [hlocal, hraw]
  · have hlocal : ¬ (0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W) :=
      fun h => hz h.1
    have hraw : ¬ ((X : ℤ) ≤ z ∧ z < (X : ℤ) ^ 2 ∧ IsCoprime z (W : ℤ)) := by
      intro h
      exact hz (le_trans (by exact_mod_cast (Nat.zero_le X)) h.1)
    simp [hlocal, hraw]

private lemma translationLaw_apply_nonneg (X W : ℕ) (hX : 0 < X) (z : ℤ) :
    0 ≤ (OAI.HarmonicTranslation.law X W) z := by
  have hmass : 0 ≤ OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) :=
    OAI.HarmonicTranslation.mass_nonneg _
      (fun y => OAI.HarmonicTranslation.raw_nonneg hX y)
  change 0 ≤ (OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W))⁻¹ •
    OAI.HarmonicTranslation.raw X W z
  rw [smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hmass)
    (OAI.HarmonicTranslation.raw_nonneg hX z)

private lemma translationLaw_mass_le_one (X W : ℕ) (hX : 0 < X) :
    OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.law X W) ≤ 1 := by
  have hraw : 0 ≤ OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) :=
    OAI.HarmonicTranslation.mass_nonneg _
      (fun y => OAI.HarmonicTranslation.raw_nonneg hX y)
  change OAI.HarmonicTranslation.mass
      ((OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W))⁻¹ •
        OAI.HarmonicTranslation.raw X W) ≤ 1
  rw [OAI.HarmonicTranslation.mass_smul]
  by_cases hzero : OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) = 0
  · simp [hzero]
  · have hpos : 0 < OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.raw X W) :=
      lt_of_le_of_ne hraw (Ne.symm hzero)
    rw [inv_mul_cancel₀ (ne_of_gt hpos)]

private lemma translationLaw_l1_le_one (X W : ℕ) (hX : 0 < X) :
    OAI.HarmonicTranslation.l1 (OAI.HarmonicTranslation.law X W) ≤ 1 := by
  have hnonneg (z : ℤ) : 0 ≤ (OAI.HarmonicTranslation.law X W) z :=
    translationLaw_apply_nonneg X W hX z
  have heq : OAI.HarmonicTranslation.l1 (OAI.HarmonicTranslation.law X W) =
      OAI.HarmonicTranslation.mass (OAI.HarmonicTranslation.law X W) := by
    change (∑ z ∈ (OAI.HarmonicTranslation.law X W).support,
        |(OAI.HarmonicTranslation.law X W) z|) =
      ∑ z ∈ (OAI.HarmonicTranslation.law X W).support,
        (OAI.HarmonicTranslation.law X W) z
    apply Finset.sum_congr rfl
    intro z hz
    exact abs_of_nonneg (hnonneg z)
  rw [heq]
  exact translationLaw_mass_le_one X W hX

private lemma translationEval_nonneg (X W : ℕ) (hX : 0 < X) (f : ℤ → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    0 ≤ OAI.HarmonicTranslation.eval (OAI.HarmonicTranslation.law X W) f := by
  unfold OAI.HarmonicTranslation.eval
  exact Finsupp.sum_nonneg fun z hz =>
    mul_nonneg (translationLaw_apply_nonneg X W hX z) (hf z)

private lemma emu_eq_translationEval {K : ℕ} (A : Parameters K)
    (i : Fin K) (N : ℕ) (f : ℤ → ℝ) :
    Emu A N i f = OAI.HarmonicTranslation.eval
      (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))) f := by
  let L := OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))
  have hX : 0 < A.X N i := A.Xpos N i
  have hpoint (z : ℤ) : mu A N i z = L z := by
    simpa [L, mu] using
      harmonicLaw_eq_translationLaw (A.X N i) (primorial (N + 1)) hX z
  have hfun : (fun z : ℤ => mu A N i z * f z) = fun z => L z * f z := by
    funext z
    rw [hpoint]
  unfold Emu
  rw [hfun]
  rw [tsum_eq_sum (s := L.support) ?_]
  · simp [L, OAI.HarmonicTranslation.eval, Finsupp.sum]
  · intro z hz
    have hz0 : L z = 0 := by
      by_contra hne
      exact hz (Finsupp.mem_support_iff.mpr hne)
    simp [hz0]

private lemma emu_abs_le {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K) (f : ℤ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z, |f z| ≤ C) :
    |Emu A N i f| ≤ C := by
  rw [emu_eq_translationEval A i N f]
  have hX : 0 < A.X N i := A.Xpos N i
  calc
    |OAI.HarmonicTranslation.eval
        (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))) f|
        ≤ OAI.HarmonicTranslation.l1
            (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))) * C :=
          OAI.HarmonicTranslation.eval_bound _ f hf
    _ ≤ 1 * C :=
      mul_le_mul_of_nonneg_right
        (translationLaw_l1_le_one (A.X N i) (primorial (N + 1)) hX) hC
    _ = C := one_mul C

private lemma emu_add {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (f g : ℤ → ℝ) :
    Emu A N i (fun z => f z + g z) = Emu A N i f + Emu A N i g := by
  rw [emu_eq_translationEval A i N (fun z => f z + g z),
    emu_eq_translationEval A i N f, emu_eq_translationEval A i N g]
  simp [OAI.HarmonicTranslation.eval, Finsupp.sum, Finset.sum_add_distrib, mul_add]

private lemma emu_const_mul {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (c : ℝ) (f : ℤ → ℝ) :
    Emu A N i (fun z => c * f z) = c * Emu A N i f := by
  rw [emu_eq_translationEval A i N (fun z => c * f z), emu_eq_translationEval A i N f]
  unfold OAI.HarmonicTranslation.eval
  change (∑ z ∈ (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))).support,
      (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))) z * (c * f z)) =
    c * ∑ z ∈ (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))).support,
      (OAI.HarmonicTranslation.law (A.X N i) (primorial (N + 1))) z * f z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma ulim_const (U : Ultrafilter ℕ) (c : ℝ) :
    ulim U (fun _ : ℕ => c) = c := by
  have h : Tendsto (fun _ : ℕ => c) (U : Filter ℕ) (𝓝 c) := tendsto_const_nhds
  simpa [ulim] using h.limUnder_eq

lemma ulim_const_mul_of_abs_le (U : Ultrafilter ℕ) (c : ℝ) (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ N, |f N| ≤ C) :
    ulim U (fun N => c * f N) = c * ulim U f := by
  have hc : ∀ N, |(fun _ : ℕ => c) N| ≤ |c| := fun _ => le_rfl
  rw [ulim_mul_of_abs_le U (fun _ : ℕ => c) f |c| C hc hf, ulim_const]

def BoundedFamilies : Submodule ℝ (ℕ → ℤ → ℝ) where
  carrier := {f | ∃ C : ℝ, 0 ≤ C ∧ ∀ N z, |f N z| ≤ C}
  zero_mem' := by
    refine ⟨0, le_rfl, ?_⟩
    intro N z
    simp
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨Cf, hCf, hf⟩
    rcases hg with ⟨Cg, hCg, hg⟩
    refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
    intro N z
    calc
      |f N z + g N z| ≤ |f N z| + |g N z| := abs_add_le _ _
      _ ≤ Cf + Cg := add_le_add (hf N z) (hg N z)
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨C, hC, hf⟩
    refine ⟨|c| * C, mul_nonneg (abs_nonneg _) hC, ?_⟩
    intro N z
    calc
      |(c • f) N z| = |c| * |f N z| := by simp [Pi.smul_apply, smul_eq_mul, abs_mul]
      _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hf N z) (abs_nonneg c)

def boundedFamilyInner {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K)
    (f g : BoundedFamilies) : ℝ :=
  ulim U (fun N => Emu A N i (fun z => f.1 N z * g.1 N z))

private lemma boundedFamilyInner_sequence_bound {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f g : BoundedFamilies) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      |Emu A N i (fun z => f.1 N z * g.1 N z)| ≤ C := by
  obtain ⟨Cf, hCf, hf⟩ := f.property
  obtain ⟨Cg, hCg, hg⟩ := g.property
  refine ⟨Cf * Cg, mul_nonneg hCf hCg, ?_⟩
  intro N
  apply emu_abs_le A N i (fun z => f.1 N z * g.1 N z) (Cf * Cg)
    (mul_nonneg hCf hCg)
  intro z
  calc
    |f.1 N z * g.1 N z| = |f.1 N z| * |g.1 N z| := by rw [abs_mul]
    _ ≤ Cf * Cg := by
      calc
        |f.1 N z| * |g.1 N z| ≤ Cf * |g.1 N z| :=
          mul_le_mul_of_nonneg_right (hf N z) (abs_nonneg _)
        _ ≤ Cf * Cg := mul_le_mul_of_nonneg_left (hg N z) hCf

@[instance_reducible]
noncomputable def boundedFamilyCore {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : PreInnerProductSpace.Core ℝ BoundedFamilies where
  inner := boundedFamilyInner A U i
  conj_inner_symm f g := by
    simp [boundedFamilyInner, mul_comm]
  re_inner_nonneg f := by
    obtain ⟨C, hC, hf⟩ := f.property
    have hbound : ∀ N,
        |Emu A N i (fun z => f.1 N z * f.1 N z)| ≤ C * C := by
      intro N
      apply emu_abs_le A N i (fun z => f.1 N z * f.1 N z) (C * C)
        (mul_nonneg hC hC)
      intro z
      calc
        |f.1 N z * f.1 N z| = |f.1 N z| * |f.1 N z| := by rw [abs_mul]
        _ ≤ C * C := by
          calc
            |f.1 N z| * |f.1 N z| ≤ C * |f.1 N z| :=
              mul_le_mul_of_nonneg_right (hf N z) (abs_nonneg _)
            _ ≤ C * C := mul_le_mul_of_nonneg_left (hf N z) hC
    have hnonneg : ∀ N, 0 ≤ Emu A N i (fun z => f.1 N z * f.1 N z) := by
      intro N
      rw [emu_eq_translationEval A i N (fun z => f.1 N z * f.1 N z)]
      exact translationEval_nonneg (A.X N i) (primorial (N + 1)) (A.Xpos N i)
        (fun z => f.1 N z * f.1 N z) (fun z => mul_self_nonneg _)
    have h := ulim_nonneg_of_forall U
      (fun N => Emu A N i (fun z => f.1 N z * f.1 N z)) (C * C) hbound hnonneg
    simpa [boundedFamilyInner] using h
  add_left f g h := by
    have hseq :
        (fun N => Emu A N i (fun z => (f + g).1 N z * h.1 N z)) =
          fun N => Emu A N i (fun z => f.1 N z * h.1 N z) +
            Emu A N i (fun z => g.1 N z * h.1 N z) := by
      funext N
      have hpoint :
          (fun z => (f + g).1 N z * h.1 N z) =
            fun z => f.1 N z * h.1 N z + g.1 N z * h.1 N z := by
        funext z
        simp [add_mul]
      rw [hpoint, emu_add]
    obtain ⟨Cf, hCf, hf⟩ := boundedFamilyInner_sequence_bound A U i f h
    obtain ⟨Cg, hCg, hg⟩ := boundedFamilyInner_sequence_bound A U i g h
    change ulim U (fun N => Emu A N i (fun z => (f + g).1 N z * h.1 N z)) =
      ulim U (fun N => Emu A N i (fun z => f.1 N z * h.1 N z)) +
        ulim U (fun N => Emu A N i (fun z => g.1 N z * h.1 N z))
    rw [hseq]
    exact ulim_add_of_abs_le U _ _ Cf Cg hf hg
  smul_left f g c := by
    have hseq :
        (fun N => Emu A N i (fun z => (c • f).1 N z * g.1 N z)) =
          fun N => c * Emu A N i (fun z => f.1 N z * g.1 N z) := by
      funext N
      have hpoint :
          (fun z => (c • f).1 N z * g.1 N z) =
            fun z => c * (f.1 N z * g.1 N z) := by
        funext z
        simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [hpoint, emu_const_mul]
    obtain ⟨C, hC, hf⟩ := boundedFamilyInner_sequence_bound A U i f g
    change ulim U (fun N => Emu A N i (fun z => (c • f).1 N z * g.1 N z)) =
      c * ulim U (fun N => Emu A N i (fun z => f.1 N z * g.1 N z))
    rw [hseq, ulim_const_mul_of_abs_le U c _ C hf]

def FamilySpace {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K) : Type :=
  BoundedFamilies

instance familySpaceAddCommGroup {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : AddCommGroup (FamilySpace A U i) := by
  change AddCommGroup BoundedFamilies
  infer_instance

instance familySpaceModule {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : Module ℝ (FamilySpace A U i) := by
  change Module ℝ BoundedFamilies
  infer_instance

noncomputable instance familySpaceInnerInstance {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : Inner ℝ (FamilySpace A U i) where
  inner := boundedFamilyInner A U i

noncomputable instance familySpaceCore {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : PreInnerProductSpace.Core ℝ (FamilySpace A U i) := boundedFamilyCore A U i

noncomputable instance familySpaceSeminormedAddCommGroup {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) : SeminormedAddCommGroup (FamilySpace A U i) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

abbrev familySpaceInner {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K)
    (f g : FamilySpace A U i) : ℝ :=
  boundedFamilyInner A U i f g

noncomputable instance familySpaceNormedSpace {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) : NormedSpace ℝ (FamilySpace A U i) :=
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)

private lemma familySpaceInner_eq_left_of_inseparable {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f f' g : FamilySpace A U i)
    (hff' : Inseparable f f') :
    boundedFamilyInner A U i f g = boundedFamilyInner A U i f' g := by
  have hdist : dist f f' = 0 := (Metric.inseparable_iff).mp hff'
  have hnorm : ‖f - f'‖ = 0 := by simpa [dist_eq_norm] using hdist
  have hcs := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) (f - f') g
  have hinnerNorm : ‖inner ℝ (f - f') g‖ = 0 := by
    apply le_antisymm
    · calc
        ‖inner ℝ (f - f') g‖ ≤ ‖f - f'‖ * ‖g‖ := hcs
        _ = 0 := by simp [hnorm]
    · exact norm_nonneg _
  have hinner : boundedFamilyInner A U i (f - f') g = 0 := by
    change inner ℝ (f - f') g = 0
    exact norm_eq_zero.mp hinnerNorm
  have hadd := (boundedFamilyCore A U i).add_left f (-f') g
  have hadd' : boundedFamilyInner A U i (f + -f') g =
      boundedFamilyInner A U i f g + boundedFamilyInner A U i (-f') g := by
    change boundedFamilyInner A U i (f + -f') g =
      boundedFamilyInner A U i f g + boundedFamilyInner A U i (-f') g at hadd
    exact hadd
  have hneg := (boundedFamilyCore A U i).smul_left f' g (-1)
  have hconj : (starRingEnd ℝ) (-1 : ℝ) = -1 := by simp
  have hneg' : boundedFamilyInner A U i (-f') g = -boundedFamilyInner A U i f' g := by
    have hnegB : boundedFamilyInner A U i ((-1 : ℝ) • f') g =
        -boundedFamilyInner A U i f' g := by
      change inner ℝ ((-1 : ℝ) • f') g = -inner ℝ f' g
      calc
        inner ℝ ((-1 : ℝ) • f') g = (starRingEnd ℝ) (-1 : ℝ) * inner ℝ f' g := hneg
        _ = -inner ℝ f' g := by rw [hconj]; ring
    simpa only [neg_one_smul] using hnegB
  have hdecomp : boundedFamilyInner A U i (f - f') g =
      boundedFamilyInner A U i f g - boundedFamilyInner A U i f' g := by
    calc
      boundedFamilyInner A U i (f - f') g =
          boundedFamilyInner A U i (f + -f') g := by rw [sub_eq_add_neg]
      _ = boundedFamilyInner A U i f g + boundedFamilyInner A U i (-f') g := hadd'
      _ = boundedFamilyInner A U i f g - boundedFamilyInner A U i f' g := by
        rw [hneg']
        ring
  rw [hdecomp] at hinner
  change boundedFamilyInner A U i f g = boundedFamilyInner A U i f' g
  exact sub_eq_zero.mp hinner

private lemma familySpaceInner_symm {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (f g : FamilySpace A U i) :
    boundedFamilyInner A U i f g = boundedFamilyInner A U i g f := by
  have hseq : (fun N => Emu A N i (fun z => f.1 N z * g.1 N z)) =
      fun N => Emu A N i (fun z => g.1 N z * f.1 N z) := by
    funext N
    have hpoint : (fun z => f.1 N z * g.1 N z) =
        fun z => g.1 N z * f.1 N z := by
      funext z
      exact mul_comm _ _
    rw [hpoint]
  change ulim U (fun N => Emu A N i (fun z => f.1 N z * g.1 N z)) =
    ulim U (fun N => Emu A N i (fun z => g.1 N z * f.1 N z))
  exact congrArg (ulim U) hseq

private lemma familySpaceInner_eq_right_of_inseparable {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f g g' : FamilySpace A U i)
    (hgg' : Inseparable g g') :
    boundedFamilyInner A U i f g = boundedFamilyInner A U i f g' := by
  have h₁ : boundedFamilyInner A U i f g = boundedFamilyInner A U i g f := by
    exact familySpaceInner_symm A U i f g
  have h₂ : boundedFamilyInner A U i g f = boundedFamilyInner A U i g' f :=
    familySpaceInner_eq_left_of_inseparable A U i g g' f hgg'
  have h₃ : boundedFamilyInner A U i g' f = boundedFamilyInner A U i f g' := by
    exact familySpaceInner_symm A U i g' f
  exact h₁.trans (h₂.trans h₃)

private lemma familySpaceInner_congr_of_inseparable {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f f' g g' : FamilySpace A U i)
    (hff' : Inseparable f f') (hgg' : Inseparable g g') :
    boundedFamilyInner A U i f g = boundedFamilyInner A U i f' g' := by
  exact (familySpaceInner_eq_left_of_inseparable A U i f f' g hff').trans
    (familySpaceInner_eq_right_of_inseparable A U i f' g g' hgg')

noncomputable def familyQuotientCore {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) :
    PreInnerProductSpace.Core ℝ (SeparationQuotient (FamilySpace A U i)) where
  inner := SeparationQuotient.lift₂ (familySpaceInner A U i)
    (fun f f' g g' hff' hgg' =>
      familySpaceInner_congr_of_inseparable A U i f g f' g' hff' hgg')
  conj_inner_symm := by
    intro x y
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
    simp only [SeparationQuotient.lift₂_mk]
    exact (familySpaceCore A U i).conj_inner_symm f g
  re_inner_nonneg := by
    intro x
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    simp only [SeparationQuotient.lift₂_mk]
    exact (familySpaceCore A U i).re_inner_nonneg f
  add_left := by
    intro x y z
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
    obtain ⟨h, rfl⟩ := SeparationQuotient.surjective_mk z
    simp only [SeparationQuotient.mk_add, SeparationQuotient.lift₂_mk]
    exact (familySpaceCore A U i).add_left f g h
  smul_left := by
    intro x y c
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨g, rfl⟩ := SeparationQuotient.surjective_mk y
    simp only [SeparationQuotient.mk_smul, SeparationQuotient.lift₂_mk]
    exact (familySpaceCore A U i).smul_left f g c

noncomputable instance familyQuotientInner {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) : Inner ℝ (SeparationQuotient (FamilySpace A U i)) where
  inner := SeparationQuotient.lift₂ (familySpaceInner A U i)
    (fun f f' g g' hff' hgg' =>
      familySpaceInner_congr_of_inseparable A U i f g f' g' hff' hgg')

@[simp] private lemma familyQuotientInner_mk {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f g : FamilySpace A U i) :
    inner ℝ (SeparationQuotient.mk f) (SeparationQuotient.mk g) =
      familySpaceInner A U i f g := rfl

noncomputable instance familyQuotientNormedSpace {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) :
    NormedSpace ℝ (SeparationQuotient (FamilySpace A U i)) :=
  SeparationQuotient.instNormedSpace

noncomputable instance familyQuotientInnerProductSpace {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) :
    InnerProductSpace ℝ (SeparationQuotient (FamilySpace A U i)) where
  norm_sq_eq_re_inner := by
    intro x
    obtain ⟨f, rfl⟩ := SeparationQuotient.surjective_mk x
    simp only [SeparationQuotient.norm_mk, familyQuotientInner_mk]
    change ‖f‖ ^ 2 = RCLike.re ((familySpaceCore A U i).inner f f)
    simpa [pow_two] using
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (𝕜 := ℝ) f).symm
  conj_inner_symm := (familyQuotientCore A U i).conj_inner_symm
  add_left := (familyQuotientCore A U i).add_left
  smul_left := (familyQuotientCore A U i).smul_left

abbrev FamilyHilbertSpace {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K) :=
  UniformSpace.Completion (SeparationQuotient (FamilySpace A U i))

def familyToHilbert {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K)
    (f : FamilySpace A U i) : FamilyHilbertSpace A U i := by
  let q : SeparationQuotient (FamilySpace A U i) := SeparationQuotient.mk f
  exact (q : FamilyHilbertSpace A U i)

def familyToHilbertLinear {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K) :
    FamilySpace A U i →ₗ[ℝ] FamilyHilbertSpace A U i where
  toFun := familyToHilbert A U i
  map_add' := by
    intro f g
    simp [familyToHilbert, SeparationQuotient.mk_add, UniformSpace.Completion.coe_add]
  map_smul' := by
    intro c f
    simp [familyToHilbert, SeparationQuotient.mk_smul, UniformSpace.Completion.coe_smul]

def boundedSubmoduleToHilbertLinear {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (S : Submodule ℝ (ℕ → ℤ → ℝ)) (hS : S ≤ BoundedFamilies) :
    S →ₗ[ℝ] FamilyHilbertSpace A U i where
  toFun x := familyToHilbert A U i ⟨x.1, hS x.2⟩
  map_add' := by
    intro x y
    let bx : FamilySpace A U i := ⟨x.1, hS x.2⟩
    let byy : FamilySpace A U i := ⟨y.1, hS y.2⟩
    have hxy : (⟨(x + y).1, hS (x + y).2⟩ : FamilySpace A U i) = bx + byy := by
      apply Subtype.ext
      rfl
    change familyToHilbert A U i ⟨(x + y).1, hS (x + y).2⟩ =
      familyToHilbert A U i bx + familyToHilbert A U i byy
    rw [hxy]
    exact (familyToHilbertLinear A U i).map_add bx byy
  map_smul' := by
    intro c x
    let bx : FamilySpace A U i := ⟨x.1, hS x.2⟩
    have hx : (⟨(c • x).1, hS (c • x).2⟩ : FamilySpace A U i) = c • bx := by
      apply Subtype.ext
      rfl
    change familyToHilbert A U i ⟨(c • x).1, hS (c • x).2⟩ =
      c • familyToHilbert A U i bx
    rw [hx]
    exact (familyToHilbertLinear A U i).map_smul c bx

lemma familyToHilbert_inner {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K)
    (f g : FamilySpace A U i) :
    inner ℝ (familyToHilbert A U i f) (familyToHilbert A U i g) =
      familySpaceInner A U i f g := by
  simp [familyToHilbert, UniformSpace.Completion.inner_coe, familyQuotientInner_mk]

lemma repFamily_eval_mem_Icc {K : ℕ} {A : Parameters K} {l : Fin K} {s : ℕ}
    {Fm : Menu s} {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (N : ℕ) (y : ℤ) :
    Φ.eval N y ∈ Set.Icc (0 : ℝ) 1 := by
  let P := Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))
  change P.eval ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) ∈ Set.Icc (0 : ℝ) 1
  exact P.range (P.g ^ ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)

lemma repFamily_eval_abs_le_one {K : ℕ} {A : Parameters K} {l : Fin K} {s : ℕ}
    {Fm : Menu s} {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (N : ℕ) (y : ℤ) :
    |Φ.eval N y| ≤ 1 := by
  have h := repFamily_eval_mem_Icc Φ N y
  rw [abs_of_nonneg h.1]
  exact h.2

lemma familyToHilbert_inner_self {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (f : FamilySpace A U i) :
    inner ℝ (familyToHilbert A U i f) (familyToHilbert A U i f) =
      boundedFamilyInner A U i f f := by
  exact familyToHilbert_inner A U i f f

lemma familyToHilbert_norm_sq {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (f : FamilySpace A U i) :
    ‖familyToHilbert A U i f‖ ^ 2 = boundedFamilyInner A U i f f := by
  have h := real_inner_self_eq_norm_mul_norm (familyToHilbert A U i f)
  rw [familyToHilbert_inner_self] at h
  simpa [pow_two] using h.symm

lemma real_inner_le_norm_of_norm_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) (hy : ‖y‖ ≤ 1) :
    inner ℝ x y ≤ ‖x‖ := by
  have hcs := norm_inner_le_norm (𝕜 := ℝ) x y
  calc
    inner ℝ x y ≤ ‖inner ℝ x y‖ := le_abs_self _
    _ ≤ ‖x‖ * ‖y‖ := hcs
    _ ≤ ‖x‖ := by nlinarith [norm_nonneg x]

lemma real_inner_le_starProjection_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (x y : E) (hy : y ∈ S) (hyn : ‖y‖ ≤ 1) :
    inner ℝ x y ≤ ‖S.starProjection x‖ := by
  have horth := S.starProjection_inner_eq_zero x y hy
  have hinner : inner ℝ x y = inner ℝ (S.starProjection x) y := by
    calc
      inner ℝ x y = inner ℝ (S.starProjection x + (x - S.starProjection x)) y := by
        congr 1
        abel
      _ = inner ℝ (S.starProjection x) y + inner ℝ (x - S.starProjection x) y :=
        inner_add_left _ _ _
      _ = inner ℝ (S.starProjection x) y := by rw [horth, add_zero]
  rw [hinner]
  exact real_inner_le_norm_of_norm_le_one (S.starProjection x) y hyn

lemma starProjection_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Submodule ℝ E) [S.HasOrthogonalProjection] (x : E) :
    ‖S.starProjection x‖ ≤ ‖x‖ := by
  let p := S.starProjection x
  have horth := S.starProjection_inner_eq_zero x p (S.starProjection_apply_mem x)
  have horth' : inner ℝ p (x - p) = 0 := by
    rw [real_inner_comm]
    exact horth
  have hdecomp : x = p + (x - p) := by abel
  have hsq : ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖x - p‖ ^ 2 := by
    rw [hdecomp]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (x-p) horth'
  nlinarith [norm_nonneg p, norm_nonneg x, sq_nonneg ‖x-p‖]

def clip01 (x : ℝ) : ℝ := min 1 (max 0 x)

lemma clip01_lipschitz : LipschitzWith 1 clip01 := by
  have h := (LipschitzWith.id.const_min 1).comp (LipschitzWith.id.const_max 0)
  have h' : LipschitzWith 1
      ((fun z : ℝ => min 1 z) ∘ fun x : ℝ => max 0 x) := by
    simpa only [one_mul, Function.id_def] using h
  have heq : (fun z : ℝ => min 1 z) ∘ (fun x : ℝ => max 0 x) = clip01 := by
    funext x
    rfl
  rw [← heq]
  exact h'

lemma clip01_mem_Icc (x : ℝ) : clip01 x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

lemma abs_clip01_sub_le {x y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |clip01 x - y| ≤ |x - y| := by
  by_cases hx0 : x < 0
  · have hclip : clip01 x = 0 := by
      simp [clip01, max_eq_left (le_of_lt hx0)]
    rw [hclip]
    have hxy : x - y ≤ 0 := by linarith [hy.1]
    have hleft : |0 - y| = y := by
      rw [abs_of_nonpos (by linarith [hy.1] : (0 : ℝ) - y ≤ 0)]
      ring
    have hright : |x - y| = y - x := by
      calc
        |x - y| = -(x - y) := abs_of_nonpos hxy
        _ = y - x := by ring
    rw [hleft, hright]
    linarith
  · by_cases hx1 : 1 < x
    · have hclip : clip01 x = 1 := by
        simp [clip01, max_eq_right (le_of_not_gt hx0), min_eq_left (le_of_lt hx1)]
      rw [hclip]
      have hyx : 0 ≤ x - y := by linarith [hy.2]
      have hleft : |1 - y| = 1 - y := abs_of_nonneg (by linarith [hy.2])
      have hright : |x - y| = x - y := abs_of_nonneg hyx
      rw [hleft, hright]
      linarith
    · have hxlo : 0 ≤ x := le_of_not_gt hx0
      have hxhi : x ≤ 1 := le_of_not_gt hx1
      have hclip : clip01 x = x := by
        simp [clip01, max_eq_right hxlo, min_eq_right hxhi]
      rw [hclip]

lemma submodule_inner_unit_sup_eq_projection_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (S : Submodule ℝ E) (x : E) :
    sSup ((fun u : E => inner ℝ x u) '' {u | u ∈ S ∧ ‖u‖ ≤ 1}) =
      ‖S.topologicalClosure.starProjection x‖ := by
  let Q := S.topologicalClosure
  let p := Q.starProjection x
  let R := ‖p‖
  let unit : Set E := {u | u ∈ S ∧ ‖u‖ ≤ 1}
  let vals : Set ℝ := (fun u : E => inner ℝ x u) '' unit
  change sSup vals = R
  have hunit : unit.Nonempty := ⟨0, ⟨S.zero_mem, by simp⟩⟩
  have hvals : vals.Nonempty := hunit.image _
  have hupper : ∀ a ∈ vals, a ≤ R := by
    rintro a ⟨u, ⟨huS, hun⟩, rfl⟩
    exact real_inner_le_starProjection_norm Q x u
      (S.le_topologicalClosure huS) hun
  have hbdd : BddAbove vals := ⟨R, hupper⟩
  have hsup_le : sSup vals ≤ R := csSup_le hvals hupper
  have hzero : 0 ≤ sSup vals := by
    have hmem : (0 : ℝ) ∈ vals := by
      have hz : (0 : E) ∈ unit := ⟨S.zero_mem, by simp⟩
      simpa [vals] using Set.mem_image_of_mem (fun u : E => inner ℝ x u) hz
    exact le_csSup hbdd hmem
  apply le_antisymm hsup_le
  by_contra hnot
  have hsup_lt : sSup vals < R := lt_of_not_ge hnot
  have hRpos : 0 < R := lt_of_le_of_lt hzero hsup_lt
  let δ := (R - sSup vals) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδR : δ < R := by dsimp [δ]; linarith
  have hpQ : p ∈ Q := by
    exact Q.starProjection_apply_mem x
  have hpcl : p ∈ closure (S : Set E) := by
    change p ∈ (S.topologicalClosure : Set E) at hpQ
    rw [Submodule.topologicalClosure_coe] at hpQ
    exact hpQ
  obtain ⟨v, hvS, hvclose⟩ := (Metric.mem_closure_iff.mp hpcl) δ hδ
  have hvnorm : ‖v - p‖ < δ := by simpa [dist_eq_norm, norm_sub_rev] using hvclose
  have hdle : ‖v‖ ≤ R + δ := by
    have hdecomp : v = (v - p) + p := by abel
    calc
      ‖v‖ = ‖(v - p) + p‖ := congrArg norm hdecomp
      _ ≤ ‖v - p‖ + ‖p‖ := norm_add_le _ _
      _ ≤ δ + R := add_le_add (le_of_lt hvnorm) (le_rfl)
      _ = R + δ := add_comm _ _
  have hRle : R < ‖v‖ + δ := by
    have hdecomp : p = (p - v) + v := by abel
    calc
      R = ‖(p - v) + v‖ := by
        change ‖p‖ = ‖(p - v) + v‖
        exact congrArg norm hdecomp
      _ ≤ ‖p - v‖ + ‖v‖ := norm_add_le _ _
      _ = ‖v - p‖ + ‖v‖ := by rw [norm_sub_rev]
      _ < δ + ‖v‖ := by
        have h := add_lt_add_left hvnorm ‖v‖
        simpa [add_comm] using h
      _ = ‖v‖ + δ := add_comm _ _
  have hδlt : δ < R := hδR
  have hvalPos : 0 < ‖v‖ := by linarith
  let u := (‖v‖⁻¹ : ℝ) • v
  have huS : u ∈ S := S.smul_mem _ hvS
  have hun : ‖u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvalPos)]
    exact inv_mul_cancel₀ (ne_of_gt hvalPos)
  have hunle : ‖u‖ ≤ 1 := hun.le
  have horth := Q.starProjection_inner_eq_zero x u (S.le_topologicalClosure huS)
  have hxinner : inner ℝ x u = inner ℝ p u := by
    calc
      inner ℝ x u = inner ℝ (p + (x - p)) u := by congr 1; abel
      _ = inner ℝ p u + inner ℝ (x - p) u := inner_add_left _ _ _
      _ = inner ℝ p u := by rw [horth, add_zero]
  have hscale : inner ℝ p u = (‖v‖⁻¹ : ℝ) * inner ℝ p v := by
    simp [u, inner_smul_right]
  have hlinear : inner ℝ p v - inner ℝ p p = inner ℝ p (v - p) := by
    exact (inner_sub_right p v p).symm
  have herror : |inner ℝ p v - inner ℝ p p| ≤ R * δ := by
    calc
      |inner ℝ p v - inner ℝ p p| = ‖inner ℝ p (v - p)‖ := by
        rw [hlinear, Real.norm_eq_abs]
      _ ≤ ‖p‖ * ‖v - p‖ := norm_inner_le_norm p (v - p)
      _ ≤ R * δ := mul_le_mul_of_nonneg_left (le_of_lt hvnorm) (norm_nonneg p)
  have hself : inner ℝ p p = R * R := by
    change inner ℝ p p = ‖p‖ * ‖p‖
    exact real_inner_self_eq_norm_mul_norm p
  have hinnerLower : R * R - R * δ ≤ inner ℝ p v := by
    have habs := (abs_le.mp herror).1
    rw [hself] at habs
    linarith
  have hnumNonneg : 0 ≤ R * R - R * δ := by nlinarith
  have hratio : (R * R - R * δ) / (R + δ) ≤ inner ℝ p v / ‖v‖ := by
    apply (div_le_div_iff₀ (by positivity : 0 < R + δ) hvalPos).2
    calc
      (R * R - R * δ) * ‖v‖ ≤ (R * R - R * δ) * (R + δ) :=
        mul_le_mul_of_nonneg_left hdle hnumNonneg
      _ ≤ inner ℝ p v * (R + δ) :=
        mul_le_mul_of_nonneg_right hinnerLower (by positivity)
  have happrox : R - 2 * δ ≤ (R * R - R * δ) / (R + δ) := by
    rw [le_div_iff₀ (by positivity : 0 < R + δ)]
    nlinarith [sq_nonneg δ]
  have hcandidate : R - 2 * δ ≤ inner ℝ x u := by
    rw [hxinner, hscale]
    calc
      R - 2 * δ ≤ (R * R - R * δ) / (R + δ) := happrox
      _ ≤ inner ℝ p v / ‖v‖ := hratio
      _ = (‖v‖⁻¹ : ℝ) * inner ℝ p v := by rw [div_eq_mul_inv, mul_comm]
  have hcandidate_gt : sSup vals < inner ℝ x u := by
    have : R - 2 * δ > sSup vals := by dsimp [δ]; linarith
    exact lt_of_lt_of_le this hcandidate
  have hmem : inner ℝ x u ∈ vals := ⟨u, ⟨huS, hunle⟩, rfl⟩
  exact (not_lt_of_ge (le_csSup hbdd hmem)) hcandidate_gt

lemma ulim_le_of_forall (U : Ultrafilter ℕ) (f g : ℕ → ℝ) (Cf Cg : ℝ)
    (hf : ∀ N, |f N| ≤ Cf) (hg : ∀ N, |g N| ≤ Cg)
    (hle : ∀ N, f N ≤ g N) : ulim U f ≤ ulim U g := by
  have hnegBound : ∀ N, |-f N| ≤ Cf := by
    intro N
    simpa using hf N
  have hdiffBound : ∀ N, |g N - f N| ≤ Cg + Cf := by
    intro N
    calc
      |g N - f N| ≤ |g N| + |f N| := abs_sub _ _
      _ ≤ Cg + Cf := add_le_add (hg N) (hf N)
  have hneg := ulim_const_mul_of_abs_le U (-1) f Cf hf
  have hsum := ulim_add_of_abs_le U g (fun N => -f N) Cg Cf hg hnegBound
  have hneg' : ulim U (fun N => -f N) = -ulim U f := by simpa using hneg
  have hdiff : ulim U (fun N => g N - f N) = ulim U g - ulim U f := by
    calc
      ulim U (fun N => g N - f N) = ulim U (fun N => g N + -f N) := by rfl
      _ = ulim U g + ulim U (fun N => -f N) := hsum
      _ = ulim U g - ulim U f := by rw [hneg']; ring
  have hpos : 0 ≤ ulim U (fun N => g N - f N) :=
    ulim_nonneg_of_forall U (fun N => g N - f N) (Cg + Cf) hdiffBound
      (fun N => sub_nonneg.mpr (hle N))
  rw [hdiff] at hpos
  linarith

lemma familyToHilbert_norm_le_one_of_unitValued {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f : FamilySpace A U i)
    (hf : ∀ N z, f.1 N z ∈ Set.Icc (0 : ℝ) 1) :
    ‖familyToHilbert A U i f‖ ≤ 1 := by
  have hseq : ∀ N, |Emu A N i (fun z => f.1 N z * f.1 N z)| ≤ 1 := by
    intro N
    apply emu_abs_le A N i (fun z => f.1 N z * f.1 N z) 1 (by norm_num)
    intro z
    have hz := hf N z
    rw [abs_of_nonneg (mul_nonneg hz.1 hz.1)]
    calc
      f.1 N z * f.1 N z ≤ 1 * f.1 N z :=
        mul_le_mul_of_nonneg_right hz.2 hz.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hz.2 (by norm_num)
      _ = 1 := by ring
  have hlim : ulim U (fun N => Emu A N i (fun z => f.1 N z * f.1 N z)) ≤ 1 := by
    have h := ulim_le_of_forall U
      (fun N => Emu A N i (fun z => f.1 N z * f.1 N z)) (fun _ => 1) 1 1
      hseq (fun _ => by norm_num) (fun N => (abs_le.mp (hseq N)).2)
    simpa only [ulim_const] using h
  have hinner : boundedFamilyInner A U i f f ≤ 1 := hlim
  rw [← familyToHilbert_norm_sq] at hinner
  nlinarith [norm_nonneg (familyToHilbert A U i f)]

private lemma emu_mono {K : ℕ} (A : Parameters K) (N : ℕ) (i : Fin K)
    (f g : ℤ → ℝ) (hfg : ∀ z, f z ≤ g z) : Emu A N i f ≤ Emu A N i g := by
  rw [emu_eq_translationEval A i N f, emu_eq_translationEval A i N g]
  unfold OAI.HarmonicTranslation.eval
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left (hfg z)
    (translationLaw_apply_nonneg (A.X N i) (primorial (N + 1)) (A.Xpos N i) z)

private lemma boundedFamilyInner_mono_sq {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (f g : FamilySpace A U i)
    (hfg : ∀ N z, |f.1 N z| ≤ |g.1 N z|) :
    boundedFamilyInner A U i f f ≤ boundedFamilyInner A U i g g := by
  obtain ⟨Cf, hCf, hf⟩ := boundedFamilyInner_sequence_bound A U i f f
  obtain ⟨Cg, hCg, hg⟩ := boundedFamilyInner_sequence_bound A U i g g
  change ulim U (fun N => Emu A N i (fun z => f.1 N z * f.1 N z)) ≤
    ulim U (fun N => Emu A N i (fun z => g.1 N z * g.1 N z))
  apply ulim_le_of_forall U _ _ Cf Cg hf hg
  intro N
  apply emu_mono A N i (fun z => f.1 N z * f.1 N z)
    (fun z => g.1 N z * g.1 N z)
  intro z
  have hsquare := (sq_le_sq₀ (abs_nonneg (f.1 N z)) (abs_nonneg (g.1 N z))).2
    (hfg N z)
  simpa [sq_abs, pow_two] using hsquare

def familySubClip {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K)
    (F G : FamilySpace A U i) (hF : ∀ N z, F.1 N z ∈ Set.Icc (0 : ℝ) 1) :
    FamilySpace A U i := by
  refine ⟨fun N z => F.1 N z - clip01 (G.1 N z), ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  intro N z
  have hclip := clip01_mem_Icc (G.1 N z)
  apply abs_le.mpr
  constructor
  · have h := hF N z
    linarith [h.1, hclip.2]
  · have h := hF N z
    linarith [h.2, hclip.1]

lemma familyToHilbert_clip_contraction {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (F G : FamilySpace A U i)
    (hF : ∀ N z, F.1 N z ∈ Set.Icc (0 : ℝ) 1) :
    ‖familyToHilbert A U i (familySubClip A U i F G hF)‖ ≤
      ‖familyToHilbert A U i (F - G)‖ := by
  have hpoint : ∀ N z,
      |(familySubClip A U i F G hF).1 N z| ≤ |(F - G).1 N z| := by
    intro N z
    simp only [familySubClip, Subtype.coe_mk, Pi.sub_apply]
    change |F.1 N z - clip01 (G.1 N z)| ≤ |F.1 N z - G.1 N z|
    calc
      |F.1 N z - clip01 (G.1 N z)| = |clip01 (G.1 N z) - F.1 N z| := by
        rw [abs_sub_comm]
      _ ≤ |G.1 N z - F.1 N z| := abs_clip01_sub_le (hF N z)
      _ = |F.1 N z - G.1 N z| := by rw [abs_sub_comm]
  have hsq := boundedFamilyInner_mono_sq A U i
    (familySubClip A U i F G hF) (F - G) hpoint
  rw [← familyToHilbert_norm_sq A U i (familySubClip A U i F G hF),
    ← familyToHilbert_norm_sq A U i (F - G)] at hsq
  nlinarith [norm_nonneg (familyToHilbert A U i (familySubClip A U i F G hF)),
    norm_nonneg (familyToHilbert A U i (F - G))]

lemma boundedSubmodule_unit_sup_eq_projection_norm {K : ℕ} (A : Parameters K)
    (U : Ultrafilter ℕ) (i : Fin K) (S : Submodule ℝ (ℕ → ℤ → ℝ))
    (hS : S ≤ BoundedFamilies) (f : FamilySpace A U i) :
    sSup ((fun u : S => boundedFamilyInner A U i f
          ⟨u.1, hS u.2⟩) ''
        {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩ ⟨u.1, hS u.2⟩ ≤ 1}) =
      ‖((boundedSubmoduleToHilbertLinear A U i S hS).range).topologicalClosure.starProjection
        (familyToHilbert A U i f)‖ := by
  let T := boundedSubmoduleToHilbertLinear A U i S hS
  let R := T.range
  let x := familyToHilbert A U i f
  let source : Set ℝ := (fun u : S => boundedFamilyInner A U i f
      ⟨u.1, hS u.2⟩) ''
    {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩ ⟨u.1, hS u.2⟩ ≤ 1}
  let target : Set ℝ := (fun y : FamilyHilbertSpace A U i => inner ℝ x y) ''
    {y | y ∈ R ∧ ‖y‖ ≤ 1}
  have himage : source = target := by
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      let b : FamilySpace A U i := ⟨u.1, hS u.2⟩
      have hT : T u = familyToHilbert A U i b := rfl
      have hn : ‖T u‖ ≤ 1 := by
        have hsq := familyToHilbert_norm_sq A U i b
        rw [← hT] at hsq
        have hnonneg : 0 ≤ ‖T u‖ := norm_nonneg _
        change boundedFamilyInner A U i b b ≤ 1 at hu
        nlinarith [hsq, hu, hnonneg]
      refine ⟨T u, ⟨?_, hn⟩, ?_⟩
      · exact ⟨u, rfl⟩
      · simpa [source, target, x, b, hT] using familyToHilbert_inner A U i f b
    · rintro ⟨y, ⟨hyR, hyn⟩, rfl⟩
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hyR
      let b : FamilySpace A U i := ⟨u.1, hS u.2⟩
      have hT : T u = familyToHilbert A U i b := rfl
      have hsq := familyToHilbert_norm_sq A U i b
      have hu : boundedFamilyInner A U i b b ≤ 1 := by
        rw [← hsq, ← hT]
        nlinarith [hyn, norm_nonneg (T u)]
      refine ⟨u, hu, ?_⟩
      simpa [source, target, x, b, hT] using (familyToHilbert_inner A U i f b).symm
  change sSup source = ‖R.topologicalClosure.starProjection x‖
  calc
    sSup source = sSup target := congrArg sSup himage
    _ = ‖R.topologicalClosure.starProjection x‖ :=
      submodule_inner_unit_sup_eq_projection_norm R x

lemma boundedSubmodule_range_mono {K : ℕ} (A : Parameters K) (U : Ultrafilter ℕ)
    (i : Fin K) (S T : Submodule ℝ (ℕ → ℤ → ℝ)) (hST : S ≤ T)
    (hS : S ≤ BoundedFamilies) (hT : T ≤ BoundedFamilies) :
    (boundedSubmoduleToHilbertLinear A U i S hS).range ≤
      (boundedSubmoduleToHilbertLinear A U i T hT).range := by
  intro y hy
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hy
  let v : T := ⟨u.1, hST u.2⟩
  refine ⟨v, ?_⟩
  change familyToHilbert A U i ⟨u.1, hS u.2⟩ =
    familyToHilbert A U i ⟨u.1, hT (hST u.2)⟩
  congr 1

lemma exists_finite_repFamily_combination {K s : ℕ} {A : Parameters K} {l : Fin K}
    {g : ℕ → ℤ → ℝ}
    (hg : g ∈ Submodule.span ℝ
      {v : ℕ → ℤ → ℝ | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km),
        v = Φ.eval}) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (Fm : Fin k → Menu s) (Km : Fin k → ℝ≥0)
      (Φ : ∀ j, RepFamily A l (Fm j) (Km j)),
      ∀ N y, g N y = ∑ j, c j * (Φ j).eval N y := by
  classical
  let generators : Set (ℕ → ℤ → ℝ) :=
    {v | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km), v = Φ.eval}
  have hg' : g ∈ Submodule.span ℝ generators := by simpa [generators] using hg
  obtain ⟨k, c, V, hV⟩ := (Submodule.mem_span_set').mp hg'
  choose Fm Km Φ hval using fun j => (V j).property
  refine ⟨k, c, Fm, Km, Φ, ?_⟩
  intro N y
  have hpoint := congrArg (fun f : ℕ → ℤ → ℝ => f N y) hV.symm
  simpa [Pi.smul_apply, smul_eq_mul, hval] using hpoint

lemma starProjection_sub_of_distance_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : Submodule ℝ E) [Q.HasOrthogonalProjection]
    (x y z : E) (hy : y ∈ Q) (hz : z ∈ Q) (hxy : ‖x - z‖ ≤ ‖x - y‖) :
    ‖Q.starProjection x - z‖ ≤ ‖Q.starProjection x - y‖ := by
  let p := Q.starProjection x
  have horthY : inner ℝ (x - p) (p - y) = 0 := by
    have hmem : p - y ∈ Q := Q.sub_mem (Q.starProjection_apply_mem x) hy
    exact Q.starProjection_inner_eq_zero x (p - y) hmem
  have horthZ : inner ℝ (x - p) (p - z) = 0 := by
    have hmem : p - z ∈ Q := Q.sub_mem (Q.starProjection_apply_mem x) hz
    exact Q.starProjection_inner_eq_zero x (p - z) hmem
  have hsqY : ‖x - y‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - y‖ ^ 2 := by
    rw [show x - y = (x - p) + (p - y) by abel]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthY
  have hsqZ : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - z‖ ^ 2 := by
    rw [show x - z = (x - p) + (p - z) by abel]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthZ
  have hsquares := mul_self_le_mul_self (norm_nonneg (x - z)) hxy
  have hsquares' : ‖x - z‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    simpa [pow_two] using hsquares
  rw [hsqZ, hsqY] at hsquares'
  have hprojSq : ‖p - z‖ ^ 2 ≤ ‖p - y‖ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hprojSq

lemma exists_lipschitz_clip_linearCombination {k : ℕ} (c : Fin k → ℝ) :
    ∃ L : ℝ≥0, LipschitzWith L
      (fun x : Fin k → ℝ => clip01 (∑ j, c j * x j)) := by
  let L : ℝ≥0 := ⟨∑ j : Fin k, |c j|,
    Finset.sum_nonneg fun j _ => abs_nonneg (c j)⟩
  refine ⟨L, ?_⟩
  have hlin : LipschitzWith L (fun x : Fin k → ℝ => ∑ j, c j * x j) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change |(∑ j, c j * x j) - (∑ j, c j * y j)| ≤
      (∑ j : Fin k, |c j|) * dist x y
    calc
      |(∑ j, c j * x j) - (∑ j, c j * y j)| =
          |∑ j, c j * (x j - y j)| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j, |c j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |c j| * dist (x j) (y j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, Real.dist_eq]
      _ ≤ ∑ j, |c j| * dist x y := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y j) (abs_nonneg _)
      _ = (∑ j, |c j|) * dist x y := by rw [Finset.sum_mul]
  have hcomp := clip01_lipschitz.comp hlin
  have heq : clip01 ∘ (fun x : Fin k → ℝ => ∑ j, c j * x j) =
      fun x => clip01 (∑ j, c j * x j) := by
    funext x
    rfl
  rw [← heq]
  simpa only [one_mul] using hcomp

def realEnergyBin (m : ℕ) (x : ℝ) : Fin (m + 1) :=
  ⟨min m (⌊max 0 x * (m : ℝ)⌋₊), by omega⟩

lemma realEnergyBin_eq_close {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hbin : realEnergyBin m x = realEnergyBin m y) :
    |x - y| ≤ 1 / (m : ℝ) := by
  have hxm0 : 0 ≤ x * (m : ℝ) := mul_nonneg hx.1 (by positivity)
  have hym0 : 0 ≤ y * (m : ℝ) := mul_nonneg hy.1 (by positivity)
  have hxfloorle : ⌊x * (m : ℝ)⌋₊ ≤ m := by
    have h := Nat.floor_mono (mul_le_mul_of_nonneg_right hx.2 (by positivity : 0 ≤ (m : ℝ)))
    simpa using h
  have hyfloorle : ⌊y * (m : ℝ)⌋₊ ≤ m := by
    have h := Nat.floor_mono (mul_le_mul_of_nonneg_right hy.2 (by positivity : 0 ≤ (m : ℝ)))
    simpa using h
  have hfloor : ⌊x * (m : ℝ)⌋₊ = ⌊y * (m : ℝ)⌋₊ := by
    have hval := congrArg Fin.val hbin
    simpa [realEnergyBin, max_eq_right hx.1, max_eq_right hy.1,
      Nat.min_eq_right hxfloorle, Nat.min_eq_right hyfloorle] using hval
  have hxfloor : (⌊x * (m : ℝ)⌋₊ : ℝ) ≤ x * (m : ℝ) := Nat.floor_le hxm0
  have hyfloor : (⌊y * (m : ℝ)⌋₊ : ℝ) ≤ y * (m : ℝ) := Nat.floor_le hym0
  have hxlt : x * (m : ℝ) < (⌊x * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hylt : y * (m : ℝ) < (⌊y * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxy : x - y < 1 / (m : ℝ) := by
    rw [lt_div_iff₀ (by exact_mod_cast hm)]
    rw [hfloor] at hxlt
    nlinarith
  have hyx : y - x < 1 / (m : ℝ) := by
    rw [lt_div_iff₀ (by exact_mod_cast hm)]
    rw [← hfloor] at hylt
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma exists_finset_split_max_two {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : 3 ≤ S.card) :
    ∃ (T : Finset α) (l i : α), S = insert l (insert i T) ∧ T.Nonempty ∧
      (∀ t ∈ T, t < l) ∧ l < i := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  let i := S.max' hSne
  have hi : i ∈ S := Finset.max'_mem S hSne
  let S₁ := S.erase i
  have hS₁card : S₁.card = S.card - 1 := Finset.card_erase_of_mem hi
  have hS₁ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
  let l := S₁.max' hS₁ne
  have hlS₁ : l ∈ S₁ := Finset.max'_mem S₁ hS₁ne
  let T := S₁.erase l
  have hTcard : T.card = S.card - 2 := by
    dsimp [T, S₁]
    rw [Finset.card_erase_of_mem hlS₁, hS₁card]
    omega
  have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; omega)
  have hTl : ∀ t ∈ T, t < l := by
    intro t ht
    exact S₁.lt_max'_of_mem_erase_max' hS₁ne (by simpa [T, l] using ht)
  have hlErase : l ∈ S.erase i := by simpa [S₁] using hlS₁
  have hli : l < i := S.lt_max'_of_mem_erase_max' hSne hlErase
  have hdecomp : S = insert l (insert i T) := by
    have h1 : insert i S₁ = S := Finset.insert_erase hi
    have h2 : insert l T = S₁ := Finset.insert_erase hlS₁
    calc
      S = insert i S₁ := h1.symm
      _ = insert i (insert l T) := by rw [h2]
      _ = insert l (insert i T) := Finset.insert_comm i l T
  exact ⟨T, l, i, hdecomp, hTne, hTl, hli⟩

noncomputable def finsetSplitMaxTwo {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : 3 ≤ S.card) : Finset α × α × α := by
  classical
  let hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let i := S.max' hne
  have hi : i ∈ S := Finset.max'_mem S hne
  let hne' : (S.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi]
    omega
  let l := (S.erase i).max' hne'
  exact ((S.erase i).erase l, l, i)

lemma finsetSplitMaxTwo_spec {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (hS : 3 ≤ S.card) :
    let p := finsetSplitMaxTwo S hS
    S = insert p.2.1 (insert p.2.2 p.1) ∧ p.1.Nonempty ∧
      (∀ t ∈ p.1, t < p.2.1) ∧ p.2.1 < p.2.2 :=
  by
    classical
    let hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let i := S.max' hne
    have hi : i ∈ S := Finset.max'_mem S hne
    let hne' : (S.erase i).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hi]
      omega
    let l := (S.erase i).max' hne'
    let T := (S.erase i).erase l
    have hl : l ∈ S.erase i := Finset.max'_mem _ hne'
    have hTne : T.Nonempty := by
      apply Finset.card_pos.mp
      dsimp [T]
      rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hi]
      omega
    have hdecomp : S = insert l (insert i T) := by
      have h1 : insert i (S.erase i) = S := Finset.insert_erase hi
      have h2 : insert l T = S.erase i := Finset.insert_erase hl
      calc
        S = insert i (S.erase i) := h1.symm
        _ = insert i (insert l T) := by rw [h2]
        _ = insert l (insert i T) := Finset.insert_comm i l T
    have hTl : ∀ t ∈ T, t < l := by
      intro t ht
      exact (S.erase i).lt_max'_of_mem_erase_max' hne' (by simpa [T, l] using ht)
    have hli : l < i := by
      have hlS : l ∈ S.erase i := hl
      exact S.lt_max'_of_mem_erase_max' hne hlS
    change S = insert l (insert i T) ∧ T.Nonempty ∧
      (∀ t ∈ T, t < l) ∧ l < i
    exact ⟨hdecomp, hTne, hTl, hli⟩

lemma finsetSplitMaxTwo_eq_insert {α : Type*} [LinearOrder α] [DecidableEq α]
    (T : Finset α) (l i : α) (hT : T.Nonempty)
    (hTl : ∀ t ∈ T, t < l) (hli : l < i) :
    finsetSplitMaxTwo (insert l (insert i T)) (by
      have hlnT : l ∉ T := by
        intro hlT
        exact (lt_irrefl l) (hTl l hlT)
      have hne : l ≠ i := ne_of_lt hli
      have hin : l ∉ insert i T := by simp [hlnT, hne]
      rw [Finset.card_insert_of_notMem hin,
        Finset.card_insert_of_notMem (by
          intro hiT
          exact (lt_irrefl i) ((hTl i hiT).trans hli))]
      have : 1 ≤ T.card := Finset.card_pos.mpr hT
      omega) = (T, l, i) := by
  classical
  have hlnT : l ∉ T := by
    intro hlT
    exact (lt_irrefl l) (hTl l hlT)
  have hne : l ≠ i := ne_of_lt hli
  have hin : l ∉ insert i T := by simp [hlnT, hne]
  have hiT : i ∉ T := by
    intro hiT
    exact (lt_irrefl i) ((hTl _ hiT).trans hli)
  have hneS : (insert l (insert i T)).Nonempty := by simp
  have hmaxI : (insert l (insert i T)).max' hneS = i := by
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact le_of_lt hli
      · rcases hx with rfl | hx
        · exact le_rfl
        · exact le_of_lt ((hTl x hx).trans hli)
    · exact (insert l (insert i T)).le_max' i (by simp)
  have herase : (insert l (insert i T)).erase i = insert l T := by
    rw [Finset.erase_insert_of_ne hne]
    simp [hiT]
  have hneMid : (insert l T).Nonempty := by simp
  have hmaxL : (insert l T).max' hneMid = l := by
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · exact le_of_lt (hTl x hx)
    · exact (insert l T).le_max' l (by simp)
  have hcardS : 3 ≤ (insert l (insert i T)).card := by
    rw [Finset.card_insert_of_notMem hin, Finset.card_insert_of_notMem hiT]
    have hTcard : 1 ≤ T.card := Finset.card_pos.mpr hT
    omega
  unfold finsetSplitMaxTwo
  simp only [hmaxI, herase, hmaxL]
  rw [Finset.erase_insert hlnT]

lemma nested_starProjection_energy_difference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Qlarge Qsmall : Submodule ℝ E)
    [Qlarge.HasOrthogonalProjection] [Qsmall.HasOrthogonalProjection]
    (hQS : Qlarge ≤ Qsmall) (x : E) :
    ‖Qsmall.starProjection x - Qlarge.starProjection x‖ ^ 2 =
      ‖Qsmall.starProjection x‖ ^ 2 - ‖Qlarge.starProjection x‖ ^ 2 := by
  let ps := Qsmall.starProjection x
  let pl := Qlarge.starProjection x
  have hps : ps ∈ Qsmall := Qsmall.starProjection_apply_mem x
  have hplSmall : pl ∈ Qsmall := hQS (Qlarge.starProjection_apply_mem x)
  have hpl : pl ∈ Qlarge := Qlarge.starProjection_apply_mem x
  have horthResidual : inner ℝ (x - ps) (ps - pl) = 0 := by
    exact Qsmall.starProjection_inner_eq_zero x (ps - pl) (Qsmall.sub_mem hps hplSmall)
  have horthLarge : inner ℝ pl (x - pl) = 0 := by
    rw [real_inner_comm]
    exact Qlarge.starProjection_inner_eq_zero x pl hpl
  have horthDiff : inner ℝ (x - ps) (ps - pl) = 0 := horthResidual
  have hresSq : ‖x - pl‖ ^ 2 = ‖x - ps‖ ^ 2 + ‖ps - pl‖ ^ 2 := by
    rw [show x - pl = (x - ps) + (ps - pl) by abel]
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - ps) (ps - pl) horthDiff
  have hpsSq : ‖x‖ ^ 2 = ‖ps‖ ^ 2 + ‖x - ps‖ ^ 2 := by
    rw [show x = ps + (x - ps) by abel]
    have horth : inner ℝ ps (x - ps) = 0 := by
      rw [real_inner_comm]
      exact Qsmall.starProjection_inner_eq_zero x ps hps
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ps (x-ps) horth
  have hplSq : ‖x‖ ^ 2 = ‖pl‖ ^ 2 + ‖x - pl‖ ^ 2 := by
    rw [show x = pl + (x - pl) by abel]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero pl (x-pl) horthLarge
  nlinarith [hresSq, hpsSq, hplSq]

abbrev menuProductGroup {s : ℕ} (F : Menu s) : Group F.productG := by
  letI : ∀ j, Group (F.G j) := fun j => F.group j
  infer_instance

abbrev menuProductTopology {s : ℕ} (F : Menu s) : TopologicalSpace F.productG := by
  letI : ∀ j, TopologicalSpace (F.G j) := fun j => F.topology j
  infer_instance

abbrev menuProductTopGroup {s : ℕ} (F : Menu s) : IsTopologicalGroup F.productG := by
  letI : ∀ j, Group (F.G j) := fun j => F.group j
  letI : ∀ j, TopologicalSpace (F.G j) := fun j => F.topology j
  letI : ∀ j, IsTopologicalGroup (F.G j) := fun j => F.topGroup j
  infer_instance

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
@[reducible]
def productMenuFamily {s n : ℕ} (Fm : Fin n → Menu s) : Menu s where
  size := n
  G u := (Fm u).productG
  group u := menuProductGroup (Fm u)
  topology u := menuProductTopology (Fm u)
  topGroup u := menuProductTopGroup (Fm u)
  Γ u := (Fm u).productΓ
  chart u := (Fm u).productChart
  metric u := (Fm u).productMetric
  compatible u := (Fm u).productCompatible

@[simp] lemma productMenuFamily_G {s n : ℕ} (Fm : Fin n → Menu s) (u : Fin n) :
    (productMenuFamily Fm).G u = (Fm u).productG := rfl

@[simp] lemma productMenuFamily_Gamma {s n : ℕ} (Fm : Fin n → Menu s) (u : Fin n) :
    (productMenuFamily Fm).Γ u = (Fm u).productΓ := rfl

@[simp] lemma productMenuFamily_metric {s n : ℕ} (Fm : Fin n → Menu s) (u : Fin n) :
    (productMenuFamily Fm).metric u = (Fm u).productMetric := rfl

@[simp] lemma productMenuFamily_compatible {s n : ℕ} (Fm : Fin n → Menu s) (u : Fin n) :
    (productMenuFamily Fm).compatible u = (Fm u).productCompatible := rfl

def CosetPiece.toProductMenu {s n : ℕ} {Fm : Fin n → Menu s} {u : Fin n}
    {K : ℝ≥0} (P : CosetPiece (Fm u) K) : CosetPiece (productMenuFamily Fm) K := by
  letI : Group ((Fm u).productG) := menuProductGroup (Fm u)
  letI : TopologicalSpace ((Fm u).productG) := menuProductTopology (Fm u)
  letI : IsTopologicalGroup ((Fm u).productG) := menuProductTopGroup (Fm u)
  letI : MetricSpace ((Fm u).productG ⧸ (Fm u).productΓ) :=
    (Fm u).productMetric.replaceTopology (Fm u).productCompatible
  letI : Group ((productMenuFamily Fm).G u) := menuProductGroup (Fm u)
  letI : TopologicalSpace ((productMenuFamily Fm).G u) := menuProductTopology (Fm u)
  letI : IsTopologicalGroup ((productMenuFamily Fm).G u) := menuProductTopGroup (Fm u)
  letI : MetricSpace ((productMenuFamily Fm).G u ⧸ (productMenuFamily Fm).Γ u) := by
    change MetricSpace ((Fm u).productG ⧸ (Fm u).productΓ)
    exact (Fm u).productMetric.replaceTopology (Fm u).productCompatible
  exact
    { index := u
      g := P.lift.padG
      x := QuotientGroup.mk P.lift.padX
      obs := P.lift.padObs
      lip := P.lift.pad_lip
      range := P.lift.pad_range }

lemma CosetPiece.toProductMenu_eval {s n : ℕ} {Fm : Fin n → Menu s} {u : Fin n}
    {K : ℝ≥0} (P : CosetPiece (Fm u) K) (k : ℤ) :
    (P.toProductMenu).eval k = P.eval k := by
  letI : Group ((Fm u).productG) := menuProductGroup (Fm u)
  letI : TopologicalSpace ((Fm u).productG) := menuProductTopology (Fm u)
  letI : IsTopologicalGroup ((Fm u).productG) := menuProductTopGroup (Fm u)
  letI : MetricSpace ((Fm u).productG ⧸ (Fm u).productΓ) :=
    (Fm u).productMetric.replaceTopology (Fm u).productCompatible
  letI : Group ((productMenuFamily Fm).G u) := menuProductGroup (Fm u)
  letI : TopologicalSpace ((productMenuFamily Fm).G u) := menuProductTopology (Fm u)
  letI : IsTopologicalGroup ((productMenuFamily Fm).G u) := menuProductTopGroup (Fm u)
  letI : MetricSpace ((productMenuFamily Fm).G u ⧸ (productMenuFamily Fm).Γ u) :=
    (productMenuFamily Fm).metric u |>.replaceTopology ((productMenuFamily Fm).compatible u)
  let Q := P.lift
  dsimp [CosetPiece.toProductMenu]
  change Q.padObs (Q.padG ^ k • QuotientGroup.mk Q.padX) = P.eval k
  rw [show Q.padG ^ k • QuotientGroup.mk Q.padX =
      QuotientGroup.mk (Q.padG ^ k * Q.padX) by rfl]
  rw [Q.pad_orbit]
  exact P.lift_eval k

def RepFamily.toProductMenu {K n s : ℕ} {A : Parameters K} {l : Fin K}
    {Fm : Fin n → Menu s} {u : Fin n} {Km : ℝ≥0}
    (Φ : RepFamily A l (Fm u) Km) : RepFamily A l (productMenuFamily Fm) Km where
  piece N j r := (Φ.piece N j r).toProductMenu

lemma RepFamily.toProductMenu_eval {K n s : ℕ} {A : Parameters K} {l : Fin K}
    {Fm : Fin n → Menu s} {u : Fin n} {Km : ℝ≥0}
    (Φ : RepFamily A l (Fm u) Km) (N : ℕ) (y : ℤ) :
    Φ.toProductMenu.eval N y = Φ.eval N y := by
  unfold RepFamily.eval
  exact CosetPiece.toProductMenu_eval (Φ.piece N (y / (A.H N l : ℤ))
    (y % (A.M N : ℤ))) ((y - y % (A.M N : ℤ)) / (A.M N : ℤ))

def CosetPiece.raiseLip {s : ℕ} {Fm : Menu s} {K K' : ℝ≥0}
    (P : CosetPiece Fm K) (h : K ≤ K') : CosetPiece Fm K' where
  index := P.index
  g := P.g
  x := P.x
  obs := P.obs
  lip := by
    letI : MetricSpace (Fm.G P.index ⧸ Fm.Γ P.index) :=
      (Fm.metric P.index).replaceTopology (Fm.compatible P.index)
    exact P.lip.weaken h
  range := P.range

def RepFamily.raiseLip {K s : ℕ} {A : Parameters K} {l : Fin K} {Fm : Menu s}
    {Km Km' : ℝ≥0} (Φ : RepFamily A l Fm Km) (h : Km ≤ Km') :
    RepFamily A l Fm Km' where
  piece N j r := (Φ.piece N j r).raiseLip h

end

end HindmanSumsProducts.Prediction
