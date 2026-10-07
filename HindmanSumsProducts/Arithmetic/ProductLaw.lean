import HindmanSumsProducts.Arithmetic.Sampling
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure03

open scoped BigOperators Topology
open Filter MeasureTheory

namespace HindmanSumsProducts
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Tail-product law induced by independent harmonic raw variables at the OAI cutoffs. -/
def parameterTailProductLaw {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (T : Finset (Fin n)) (σ : ℕ) : ℝ :=
  ∑' t : Fin n → ℕ,
    (if (∏ j ∈ T, t j) = σ then 1 else 0) *
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)

/-- The actual block-product mass obtained by pushing forward OpenAI's `Parameters.law`. -/
def parameterBlockProductMass {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ) : ℝ :=
  if 0 ≤ z then
    (A.law N hX).real {t : Fin n → ℕ | (∏ j ∈ B.set, t j : ℕ) = z.toNat}
  else 0

/-- The weighted pivot law `ν_B μ_i`, with `ν_B` defined locally in `Defs.lean`. -/
def weightedPivotMass {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : OAI.SourceBlocks.Block n) (z : ℤ) : ℝ :=
  nuB (parameterTailProductLaw A N B.2.val) z *
    harmonicLaw (A.X N B.1) (primorial (N + 1)) z

/-- Joint block-product mass under the OAI law, for a fixed family of blocks. -/
def parameterJointBlockProductMass {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : Fin r → OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : Fin r → ℤ) : ℝ :=
  (A.law N hX).real {t : Fin n → ℕ |
    ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat}

/-- Product of the individual weighted pivot masses for a fixed block family. -/
def weightedPivotTupleMass {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : Fin r → OAI.SourceBlocks.Block n)
    (z : Fin r → ℤ) : ℝ := ∏ d, weightedPivotMass A N (B d) (z d)

private abbrev blockCoordinateUnion {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n) : Finset (Fin n) :=
  Finset.biUnion (Finset.univ : Finset (Fin r)) (fun d => (B d).set)

private abbrev blockCoordinateType {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n) :=
  Σ d : Fin r, {j : Fin n // j ∈ (B d).set}

private abbrev outsideBlockCoordinateType {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n) :=
  {j : Fin n // j ∉ blockCoordinateUnion B}

private def blockCoordinateLabel {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n) (j : Fin n)
    (hj : j ∈ blockCoordinateUnion B) : Fin r :=
  Classical.choose (show ∃ d : Fin r, j ∈ (B d).set by
    simpa [blockCoordinateUnion] using hj)

private lemma blockCoordinateLabel_mem {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n) (j : Fin n)
    (hj : j ∈ blockCoordinateUnion B) :
    j ∈ (B (blockCoordinateLabel B j hj)).set :=
  Classical.choose_spec (show ∃ d : Fin r, j ∈ (B d).set by
    simpa [blockCoordinateUnion] using hj)

private def blockCoordinateEquiv {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set) :
    Fin n ≃ blockCoordinateType B ⊕ outsideBlockCoordinateType B where
  toFun j := by
    by_cases hj : j ∈ blockCoordinateUnion B
    · exact Sum.inl ⟨blockCoordinateLabel B j hj, ⟨j, blockCoordinateLabel_mem B j hj⟩⟩
    · exact Sum.inr ⟨j, hj⟩
  invFun q :=
    match q with
    | Sum.inl x => x.2.1
    | Sum.inr x => x.1
  left_inv j := by
    by_cases hj : j ∈ blockCoordinateUnion B
    · simp [hj]
    · simp [hj]
  right_inv q := by
    cases q with
    | inr x => simp [x.2]
    | inl x =>
        rcases x with ⟨d, j, hj⟩
        have hmem : j ∈ blockCoordinateUnion B := by
          change j ∈ (Finset.univ : Finset (Fin r)).biUnion (fun d => (B d).set)
          exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ d, hj⟩
        have hchoose : blockCoordinateLabel B j hmem = d := by
          by_contra hne
          have hother : j ∈ (B (blockCoordinateLabel B j hmem)).set :=
            blockCoordinateLabel_mem B j hmem
          have hdis := hdisj d (blockCoordinateLabel B j hmem) (Ne.symm hne)
          exact (Finset.disjoint_left.mp hdis) hj hother
        change (if h : j ∈ blockCoordinateUnion B then
          (Sum.inl (⟨blockCoordinateLabel B j h,
            ⟨j, blockCoordinateLabel_mem B j h⟩⟩ : blockCoordinateType B))
          else (Sum.inr (⟨j, h⟩ : outsideBlockCoordinateType B))) =
            (Sum.inl (⟨d, ⟨j, hj⟩⟩ : blockCoordinateType B))
        rw [dif_pos hmem]
        have hpair :
            (⟨blockCoordinateLabel B j hmem, ⟨j, blockCoordinateLabel_mem B j hmem⟩⟩ :
              blockCoordinateType B) = ⟨d, ⟨j, hj⟩⟩ := by
          cases hchoose
          rfl
        exact congrArg Sum.inl hpair

private def blockAssignmentEquiv {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set) :
    (Fin n → ℕ) ≃ ((blockCoordinateType B → ℕ) ×
      (outsideBlockCoordinateType B → ℕ)) := by
  let e := blockCoordinateEquiv B hdisj
  let e₁ : (Fin n → ℕ) ≃ ((blockCoordinateType B ⊕ outsideBlockCoordinateType B) → ℕ) := {
    toFun := fun t q => t (e.symm q)
    invFun := fun t j => t (e j)
    left_inv := by intro t; funext j; simp
    right_inv := by intro t; funext q; simp
  }
  let e₂ : ((blockCoordinateType B ⊕ outsideBlockCoordinateType B) → ℕ) ≃
      ((blockCoordinateType B → ℕ) × (outsideBlockCoordinateType B → ℕ)) := {
    toFun := fun t => (fun j => t (Sum.inl j), fun j => t (Sum.inr j))
    invFun := fun p q => match q with
      | Sum.inl j => p.1 j
      | Sum.inr j => p.2 j
    left_inv := by intro t; funext q; cases q <;> rfl
    right_inv := by intro p; apply Prod.ext <;> funext j <;> rfl
  }
  exact e₁.trans e₂

private lemma blockAssignmentEquiv_apply_block {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (t : Fin n → ℕ) (d : Fin r) (j : {j : Fin n // j ∈ (B d).set}) :
    (blockAssignmentEquiv B hdisj t).1 ⟨d, j⟩ = t j.val := by
  simp [blockAssignmentEquiv, blockCoordinateEquiv]

private lemma blockAssignmentEquiv_apply_outside {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (t : Fin n → ℕ) (j : outsideBlockCoordinateType B) :
    (blockAssignmentEquiv B hdisj t).2 j = t j.val := by
  simp [blockAssignmentEquiv, blockCoordinateEquiv]

private lemma blockAssignmentEquiv_symm_apply {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (p : (blockCoordinateType B → ℕ) × (outsideBlockCoordinateType B → ℕ))
    (j : Fin n) :
    (blockAssignmentEquiv B hdisj).symm p j =
      match blockCoordinateEquiv B hdisj j with
      | Sum.inl c => p.1 c
      | Sum.inr o => p.2 o := by
  rfl

private lemma blockCoordinateEquiv_of_mem {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (d : Fin r) (j : Fin n) (hj : j ∈ (B d).set) :
    blockCoordinateEquiv B hdisj j = Sum.inl ⟨d, ⟨j, hj⟩⟩ := by
  have hmem : j ∈ blockCoordinateUnion B := by
    change j ∈ (Finset.univ : Finset (Fin r)).biUnion (fun d => (B d).set)
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ d, hj⟩
  have hchoose : blockCoordinateLabel B j hmem = d := by
    by_contra hne
    have hother : j ∈ (B (blockCoordinateLabel B j hmem)).set :=
      blockCoordinateLabel_mem B j hmem
    have hdis := hdisj d (blockCoordinateLabel B j hmem) (Ne.symm hne)
    exact (Finset.disjoint_left.mp hdis) hj hother
  change (if h : j ∈ blockCoordinateUnion B then
      (Sum.inl (⟨blockCoordinateLabel B j h,
        ⟨j, blockCoordinateLabel_mem B j h⟩⟩ : blockCoordinateType B))
      else (Sum.inr (⟨j, h⟩ : outsideBlockCoordinateType B))) =
        (Sum.inl (⟨d, ⟨j, hj⟩⟩ : blockCoordinateType B))
  rw [dif_pos hmem]
  have hblock :
      (⟨blockCoordinateLabel B j hmem, ⟨j, blockCoordinateLabel_mem B j hmem⟩⟩ :
        blockCoordinateType B) = ⟨d, ⟨j, hj⟩⟩ := by
    cases hchoose
    rfl
  exact congrArg Sum.inl hblock

private lemma blockCoordinateEquiv_of_not_mem {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (j : outsideBlockCoordinateType B) :
    blockCoordinateEquiv B hdisj j.val = Sum.inr j := by
  have hnot : ¬ ∃ d : Fin r, j.val ∈ (B d).set := by
    intro h
    apply j.property
    change j.val ∈ (Finset.univ : Finset (Fin r)).biUnion (fun d => (B d).set)
    exact Finset.mem_biUnion.mpr ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩
  unfold blockCoordinateEquiv
  simp [blockCoordinateUnion, hnot]

private lemma blockAssignmentEquiv_symm_apply_block {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (p : (blockCoordinateType B → ℕ) × (outsideBlockCoordinateType B → ℕ))
    (d : Fin r) (j : {j : Fin n // j ∈ (B d).set}) :
    (blockAssignmentEquiv B hdisj).symm p j.val = p.1 ⟨d, j⟩ := by
  rw [blockAssignmentEquiv_symm_apply, blockCoordinateEquiv_of_mem B hdisj d j.val j.property]

private lemma blockAssignmentEquiv_symm_apply_outside {n r : ℕ}
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (p : (blockCoordinateType B → ℕ) × (outsideBlockCoordinateType B → ℕ))
    (j : outsideBlockCoordinateType B) :
    (blockAssignmentEquiv B hdisj).symm p j.val = p.2 j := by
  rw [blockAssignmentEquiv_symm_apply,
    blockCoordinateEquiv_of_not_mem B hdisj j]

private def localBlockMass {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (B : OAI.SourceBlocks.Block n) (z : ℤ) : ℝ :=
  if 0 ≤ z then
    ∑ t ∈ Fintype.piFinset (fun j : {j : Fin n // j ∈ B.set} =>
        OAI.RawHarmonicProbability.units (A.X N j.val) (primorial (N + 1))),
      if (∏ j : {j : Fin n // j ∈ B.set}, t j) = z.toNat then
        ∏ j : {j : Fin n // j ∈ B.set},
          harmonicNatLaw (A.X N j.val) (primorial (N + 1)) (t j) else 0
  else 0

private lemma blockAssignmentEquiv_mem_iff {n r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (t : Fin n → ℕ) :
    t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) ↔
      (blockAssignmentEquiv B hdisj t).1 ∈ Fintype.piFinset
          (fun c : blockCoordinateType B =>
            OAI.RawHarmonicProbability.units (A.X N c.2.1) (primorial (N + 1))) ∧
      (blockAssignmentEquiv B hdisj t).2 ∈ Fintype.piFinset
          (fun c : outsideBlockCoordinateType B =>
            OAI.RawHarmonicProbability.units (A.X N c.1) (primorial (N + 1))) := by
  classical
  let e := blockAssignmentEquiv B hdisj
  constructor
  · intro ht
    have ht' := Fintype.mem_piFinset.mp (by simpa [OAI.ProductExposureLaw.outsideDomain] using ht)
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro c
      rcases c with ⟨d, j⟩
      rw [blockAssignmentEquiv_apply_block]
      exact ht' j.val
    · apply Fintype.mem_piFinset.mpr
      intro c
      rcases c with ⟨j, hj⟩
      rw [blockAssignmentEquiv_apply_outside]
      exact ht' j
  · rintro ⟨hg, ho⟩
    have hg' := Fintype.mem_piFinset.mp hg
    have ho' := Fintype.mem_piFinset.mp ho
    apply Fintype.mem_piFinset.mpr
    intro j
    have hdecomp : t = e.symm (e t) := (e.left_inv t).symm
    rw [hdecomp, blockAssignmentEquiv_symm_apply]
    cases hcoord : blockCoordinateEquiv B hdisj j with
    | inl c =>
        have hval : j = c.2.1 := by
          calc
            j = (blockCoordinateEquiv B hdisj).symm
                (blockCoordinateEquiv B hdisj j) := (blockCoordinateEquiv B hdisj).left_inv j |>.symm
            _ = c.2.1 := by rw [hcoord]; rfl
        simpa [hval] using hg' c
    | inr c =>
        have hval : j = c.val := by
          calc
            j = (blockCoordinateEquiv B hdisj).symm
                (blockCoordinateEquiv B hdisj j) := (blockCoordinateEquiv B hdisj).left_inv j |>.symm
            _ = c.val := by rw [hcoord]; rfl
        simpa [hval] using ho' c

private lemma harmonicNatLaw_eq_singleton_mass (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) (m : ℕ) :
    harmonicNatLaw X W m =
      (OAI.RawHarmonicProbability.law X W hW hX : Measure ℕ).real {m} := by
  have hnorm : harmonicNormalizer X W = OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
    simp [harmonicNormalizer, OAI.DyadicHarmonicBoundary.mass,
      Finset.sum_filter, Nat.coprime_comm, one_div]
  rw [OAI.ProductExposureLaw.law_singleton, hnorm.symm]
  have hZpos : 0 < harmonicNormalizer X W := by
    rw [hnorm]
    exact OAI.RawHarmonicProbability.mass_pos X W hW hX
  unfold harmonicNatLaw
  by_cases h : X ≤ m ∧ m < X ^ 2 ∧ Nat.Coprime m W
  · have hmUnit : m ∈ OAI.RawHarmonicProbability.units X W := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2.symm⟩
    rw [if_pos h, if_pos hmUnit]
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < X) h.1)
    field_simp [ne_of_gt hZpos, ne_of_gt hmpos]
    <;> ring
  · have hmUnit : m ∉ OAI.RawHarmonicProbability.units X W := by
      intro hm
      rcases Finset.mem_filter.mp hm with ⟨hmIco, hcop⟩
      have hmIco' := Finset.mem_Ico.mp hmIco
      exact h ⟨hmIco'.1, hmIco'.2, hcop.symm⟩
    simp [h, hmUnit]

private lemma harmonicNatLaw_sum_units_joint (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) :
    ∑ m ∈ OAI.RawHarmonicProbability.units X W, harmonicNatLaw X W m = 1 := by
  classical
  let μ : Measure ℕ := OAI.RawHarmonicProbability.law X W hW hX
  have hmass : μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) = 1 := by
    have hEq : μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) = μ.real Set.univ := by
      apply measureReal_congr
      filter_upwards [OAI.ProductExposureLabels.law_ae_units X W hW hX] with m hm
      simp [hm]
    rw [hEq]
    simp [μ]
  calc
    _ = ∑ m ∈ OAI.RawHarmonicProbability.units X W, μ.real {m} := by
      apply Finset.sum_congr rfl
      intro m hm
      exact harmonicNatLaw_eq_singleton_mass X W hW hX m
    _ = μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) := by
      rw [sum_measureReal_singleton]
    _ = 1 := hmass

private lemma measureReal_eq_finset_sum_of_ae_mem {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure β) [IsFiniteMeasure μ]
    (S : Finset β) (hS : ∀ᵐ x ∂μ, x ∈ S) (E : Set β) :
    μ.real E = ∑ x ∈ S, if x ∈ E then μ.real {x} else 0 := by
  classical
  have hAE : μ.real E = μ.real (E ∩ (S : Set β)) := by
    apply measureReal_congr
    filter_upwards [hS] with x hx
    change (x ∈ E) = (x ∈ E ∩ (S : Set β))
    apply propext
    simp only [Set.mem_inter_iff]
    exact ⟨fun hxE => ⟨hxE, hx⟩, fun hx => hx.1⟩
  have hset : E ∩ (S : Set β) = ((S.filter fun x => x ∈ E : Finset β) : Set β) := by
    ext x
    simp [and_comm]
  calc
    μ.real E = μ.real (E ∩ (S : Set β)) := hAE
    _ = μ.real ((S.filter fun x => x ∈ E : Finset β) : Set β) := by rw [hset]
    _ = ∑ x ∈ S.filter (fun x => x ∈ E), μ.real {x} := by
      rw [← sum_measureReal_singleton]
    _ = ∑ x ∈ S, if x ∈ E then μ.real {x} else 0 := by
      rw [Finset.sum_filter]

private lemma parameter_law_singleton {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (t : Fin n → ℕ) :
    (A.law N hX).real {t} =
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
  rw [OAI.SourceAdmissible.Parameters.law]
  simp only [OAI.ProductExposureLaw.outsideLaw, measureReal_def,
    Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  symm
  exact harmonicNatLaw_eq_singleton_mass (A.X N j) (primorial (N + 1))
    (primorial_pos _) (hX j) (t j)

private lemma parameterBlockProductMass_finset {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ) :
    parameterBlockProductMass A N B hX z =
      if 0 ≤ z then
        ∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
          if (∏ j ∈ B.set, t j) = z.toNat then
            ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) else 0
      else 0 := by
  classical
  unfold parameterBlockProductMass
  by_cases hz : 0 ≤ z
  · simp only [hz, ite_true]
    rw [measureReal_eq_finset_sum_of_ae_mem
      (A.law N hX)
      (OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)))
      (OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
        (primorial_pos _) hX)
      {t | (∏ j ∈ B.set, t j) = z.toNat}]
    simp_rw [parameter_law_singleton]
    rfl
  · simp [hz]

private lemma parameterJointBlockProductMass_finset {n r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : Fin r → ℤ) :
    parameterJointBlockProductMass A N B hX z =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
        if ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat then
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) else 0 := by
  classical
  unfold parameterJointBlockProductMass
  rw [measureReal_eq_finset_sum_of_ae_mem
    (A.law N hX)
    (OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)))
    (OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
      (primorial_pos _) hX)
    {t | ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat}]
  simp_rw [parameter_law_singleton]
  rfl

set_option maxHeartbeats 1000000 in
private lemma parameterJointBlockProductMass_eq_localBlockMass_product {n r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (z : Fin r → ℤ) :
    parameterJointBlockProductMass A N B hX z =
      ∏ d, localBlockMass A N (B d) (z d) := by
  classical
  by_cases hz : ∀ d, 0 ≤ z d
  · rw [parameterJointBlockProductMass_finset]
    let U : Fin n → Finset ℕ := fun j =>
      OAI.RawHarmonicProbability.units (A.X N j) (primorial (N + 1))
    let D : Finset (Fin n → ℕ) := Fintype.piFinset U
    let G : Finset (blockCoordinateType B → ℕ) :=
      Fintype.piFinset (fun c : blockCoordinateType B => U c.2.1)
    let O : Finset (outsideBlockCoordinateType B → ℕ) :=
      Fintype.piFinset (fun c : outsideBlockCoordinateType B => U c.1)
    let e := blockAssignmentEquiv B hdisj
    let term (d : Fin r) (g : {j : Fin n // j ∈ (B d).set} → ℕ) : ℝ :=
      if (∏ j, g j) = (z d).toNat then
        ∏ j, harmonicNatLaw (A.X N j.val) (primorial (N + 1)) (g j) else 0
    let full (t : Fin n → ℕ) : ℝ :=
      if ∀ d, (∏ j ∈ (B d).set, t j) = (z d).toNat then
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) else 0
    have hmem := blockAssignmentEquiv_mem_iff A N B hdisj
    have hsumReindex (f : (Fin n → ℕ) → ℝ) :
        (∑ t ∈ D, f t) =
          ∑ g ∈ G, ∑ o ∈ O, f (e.symm (g, o)) := by
      calc
        _ = ∑ p ∈ G.product O, f (e.symm (p.1, p.2)) := by
          refine Finset.sum_bij (fun t _ => e t) ?_ ?_ ?_ ?_
          · intro t ht
            have ht' : t ∈ OAI.ProductExposureLaw.outsideDomain
                (A.X N) (primorial (N + 1)) := by
              simpa [D, OAI.ProductExposureLaw.outsideDomain] using ht
            rcases (hmem t).mp ht' with ⟨hg, ho⟩
            have hfirst : (e t).1 ∈ G := by
              change ((blockAssignmentEquiv B hdisj) t).1 ∈ G
              simpa [G, U] using hg
            have hsecond : (e t).2 ∈ O := by
              change ((blockAssignmentEquiv B hdisj) t).2 ∈ O
              simpa [O, U] using ho
            exact Finset.mem_product.mpr ⟨hfirst, hsecond⟩
          · intro t ht t' ht' heq
            exact e.injective heq
          · intro p hp
            rcases Finset.mem_product.mp hp with ⟨hg, ho⟩
            refine ⟨e.symm (p.1, p.2), ?_, ?_⟩
            · apply (hmem _).mpr
              have hfirst : ((blockAssignmentEquiv B hdisj) (e.symm (p.1, p.2))).1 ∈ G := by
                change (e (e.symm (p.1, p.2))).1 ∈ G
                rw [e.apply_symm_apply]
                exact hg
              have hsecond : ((blockAssignmentEquiv B hdisj) (e.symm (p.1, p.2))).2 ∈ O := by
                change (e (e.symm (p.1, p.2))).2 ∈ O
                rw [e.apply_symm_apply]
                exact ho
              have hpi : ((blockAssignmentEquiv B hdisj) (e.symm (p.1, p.2))).1 ∈
                  Fintype.piFinset (fun c : blockCoordinateType B => U c.2.1) ∧
                ((blockAssignmentEquiv B hdisj) (e.symm (p.1, p.2))).2 ∈
                  Fintype.piFinset (fun c : outsideBlockCoordinateType B => U c.1) := by
                simpa [G, O, U] using And.intro hfirst hsecond
              exact hpi
            · exact e.apply_symm_apply (p.1, p.2)
          · intro t ht
            exact congrArg f (e.left_inv t).symm
        _ = _ := by
          change (∑ p ∈ G ×ˢ O, f (e.symm (p.1, p.2))) = _
          exact Finset.sum_product G O (fun p => f (e.symm (p.1, p.2)))
    let w (j : Fin n) (a : ℕ) : ℝ :=
      harmonicNatLaw (A.X N j) (primorial (N + 1)) a
    have hweight (g : blockCoordinateType B → ℕ)
        (o : outsideBlockCoordinateType B → ℕ) :
        (∏ j : Fin n, w j (e.symm (g, o) j)) =
          (∏ d, ∏ j : {j : Fin n // j ∈ (B d).set},
              w j.val (g ⟨d, j⟩)) *
            ∏ j : outsideBlockCoordinateType B, w j.val (o j) := by
      let eCoord := blockCoordinateEquiv B hdisj
      let f : (blockCoordinateType B ⊕ outsideBlockCoordinateType B) → ℝ := fun c =>
        w (eCoord.symm c) (e.symm (g, o) (eCoord.symm c))
      calc
        _ = ∏ j : Fin n, f (eCoord j) := by simp [f]
        _ = ∏ c : blockCoordinateType B ⊕ outsideBlockCoordinateType B, f c :=
          eCoord.prod_comp f
        _ = _ := by
          rw [Fintype.prod_sum_type, Fintype.prod_sigma]
          dsimp [f]
          congr 1
          · apply Finset.prod_congr rfl
            intro d hd
            apply Finset.prod_congr rfl
            intro j hj
            change w j.val (e.symm (g, o) j.val) = w j.val (g ⟨d, j⟩)
            rw [blockAssignmentEquiv_symm_apply_block B hdisj (g, o) d j]
          · apply Finset.prod_congr rfl
            intro j hj
            change w j.val (e.symm (g, o) j.val) = w j.val (o j)
            rw [blockAssignmentEquiv_symm_apply_outside B hdisj (g, o) j]
    have hblockProd (g : blockCoordinateType B → ℕ)
        (o : outsideBlockCoordinateType B → ℕ) (d : Fin r) :
        (∏ j ∈ (B d).set, e.symm (g, o) j) =
          ∏ j : {j : Fin n // j ∈ (B d).set}, g ⟨d, j⟩ := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro j hj
      have he := blockCoordinateEquiv_of_mem B hdisj d j.val j.property
      change (blockAssignmentEquiv B hdisj).symm (g, o) j.val = g ⟨d, j⟩
      rw [blockAssignmentEquiv_symm_apply_block B hdisj (g, o) d j]
    have hrest :
        (∑ o ∈ O, ∏ j : outsideBlockCoordinateType B,
            w j.val (o j)) = 1 := by
      rw [show (∑ o ∈ O, ∏ j : outsideBlockCoordinateType B, w j.val (o j)) =
          ∑ o ∈ Fintype.piFinset (fun j : outsideBlockCoordinateType B => U j.1),
            ∏ j : outsideBlockCoordinateType B, w j.val (o j) by rfl]
      rw [← Finset.prod_univ_sum]
      have hcoord (j : outsideBlockCoordinateType B) :
          ∑ a ∈ U j.1, w j.1 a = 1 := by
        exact harmonicNatLaw_sum_units_joint (A.X N j.1) (primorial (N + 1))
          (primorial_pos _) (hX j.1)
      simp_rw [hcoord]
      simp
    let V : (d : Fin r) → Finset ({j : Fin n // j ∈ (B d).set} → ℕ) := fun d =>
      Fintype.piFinset (fun j : {j : Fin n // j ∈ (B d).set} => U j.val)
    let GGroups : Finset ((d : Fin r) → {j : Fin n // j ∈ (B d).set} → ℕ) :=
      Fintype.piFinset V
    let curry : (blockCoordinateType B → ℕ) ≃
        ((d : Fin r) → {j : Fin n // j ∈ (B d).set} → ℕ) :=
      Equiv.piCurry (fun d (j : {j : Fin n // j ∈ (B d).set}) => ℕ)
    have hgroupMem (g : blockCoordinateType B → ℕ) :
        g ∈ G ↔ curry g ∈ GGroups := by
      constructor
      · intro hg
        apply Fintype.mem_piFinset.mpr
        intro d
        apply Fintype.mem_piFinset.mpr
        intro j
        have hg' := Fintype.mem_piFinset.mp hg
        change g ⟨d, j⟩ ∈ U j.val
        exact hg' ⟨d, j⟩
      · intro hg
        apply Fintype.mem_piFinset.mpr
        intro c
        have hg' := Fintype.mem_piFinset.mp hg
        have h := Fintype.mem_piFinset.mp (hg' c.1) c.2
        change g ⟨c.1, c.2⟩ ∈ U c.2.1
        exact h
    let eGroup : {g : blockCoordinateType B → ℕ // g ∈ G} ≃
        {g : (d : Fin r) → {j : Fin n // j ∈ (B d).set} → ℕ // g ∈ GGroups} := {
      toFun := fun g => ⟨curry g.1, (hgroupMem g.1).mp g.2⟩
      invFun := fun g => ⟨curry.symm g.1, (hgroupMem (curry.symm g.1)).mpr (by
        simpa using g.2)⟩
      left_inv := by intro g; apply Subtype.ext; exact curry.left_inv g.1
      right_inv := by intro g; apply Subtype.ext; exact curry.right_inv g.1
    }
    have hgroupFactor :
        (∑ g ∈ G, ∏ d, term d (fun j => g ⟨d, j⟩)) =
          ∏ d, ∑ a ∈ V d, term d a := by
      calc
        _ = ∑ g : {g : blockCoordinateType B → ℕ // g ∈ G},
              ∏ d, term d (fun j => g.1 ⟨d, j⟩) := (Finset.sum_coe_sort G _).symm
        _ = ∑ g : {g : (d : Fin r) → {j : Fin n // j ∈ (B d).set} → ℕ //
              g ∈ GGroups}, ∏ d, term d (g.1 d) := by
                apply Fintype.sum_equiv eGroup
                intro g
                rfl
        _ = ∑ g ∈ GGroups, ∏ d, term d (g d) := by
              exact Finset.sum_coe_sort GGroups (fun g => ∏ d, term d (g d))
        _ = ∏ d, ∑ a ∈ V d, term d a := by
              dsimp [GGroups]
              exact (Finset.prod_univ_sum V term).symm
    have hfull (g : blockCoordinateType B → ℕ)
        (o : outsideBlockCoordinateType B → ℕ) :
        full (e.symm (g, o)) =
          (∏ d, term d (fun j => g ⟨d, j⟩)) *
            ∏ j : outsideBlockCoordinateType B, w j.val (o j) := by
      by_cases hall : ∀ d, (∏ j : {j : Fin n // j ∈ (B d).set}, g ⟨d, j⟩) =
          (z d).toNat
      · have hOrig : ∀ d, (∏ j ∈ (B d).set, e.symm (g, o) j) = (z d).toNat := by
          intro d
          rw [hblockProd g o d]
          exact hall d
        have htermProd :
            (∏ d, term d (fun j => g ⟨d, j⟩)) =
              ∏ d, ∏ j : {j : Fin n // j ∈ (B d).set},
                w j.val (g ⟨d, j⟩) := by
          apply Finset.prod_congr rfl
          intro d hd
          unfold term
          rw [if_pos (hall d)]
        calc
          _ = ∏ j, w j (e.symm (g, o) j) := by simp [full, hOrig, w]
          _ = (∏ d, ∏ j : {j : Fin n // j ∈ (B d).set},
                w j.val (g ⟨d, j⟩)) *
              ∏ j : outsideBlockCoordinateType B, w j.val (o j) := hweight g o
          _ = _ := by rw [← htermProd]
      · have ⟨d, hd⟩ := not_forall.mp hall
        have htermzero : term d (fun j => g ⟨d, j⟩) = 0 := by
          unfold term
          rw [if_neg hd]
        have hprodzero : ∏ d, term d (fun j => g ⟨d, j⟩) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ d) htermzero
        have hnotOrig :
            ¬ ∀ d, (∏ j ∈ (B d).set, e.symm (g, o) j) = (z d).toNat := by
          intro hOrigAll
          apply hall
          intro d
          have hh := hOrigAll d
          rw [hblockProd g o d] at hh
          exact hh
        calc
          _ = 0 := by simp [full, hnotOrig]
          _ = (∏ d, term d (fun j => g ⟨d, j⟩)) *
              ∏ j : outsideBlockCoordinateType B, w j.val (o j) := by
                rw [hprodzero]
                simp
    calc
      _ = ∑ t ∈ D, full t := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [full, hz]
      _ = ∑ g ∈ G, ∑ o ∈ O, full (e.symm (g, o)) := hsumReindex full
      _ = 1 * ∑ g ∈ G, ∏ d, term d (fun j => g ⟨d, j⟩) := by
            calc
              _ = ∑ g ∈ G,
                    (∏ d, term d (fun j => g ⟨d, j⟩)) *
                      (∑ o ∈ O, ∏ j : outsideBlockCoordinateType B,
                        w j.val (o j)) := by
                      apply Finset.sum_congr rfl
                      intro g hg
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro o ho
                      exact hfull g o
              _ = _ := by rw [hrest]; simp
      _ = ∏ d, localBlockMass A N (B d) (z d) := by
            rw [hgroupFactor]
            simp only [one_mul]
            apply Finset.prod_congr rfl
            intro d hd
            simp [term, localBlockMass, V, U, hz]
  · have hbad : ∃ d, ¬ 0 ≤ z d := by simpa only [not_forall] using hz
    rcases hbad with ⟨d, hd⟩
    rw [parameterJointBlockProductMass_finset]
    have hnot (t : Fin n → ℕ) :
        ¬(∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat) := by
      intro hall
      exact hd (hall d).1
    have hlhs :
        (∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
          if ∀ d, 0 ≤ z d ∧ (∏ j ∈ (B d).set, t j) = (z d).toNat then
            ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [hnot t]
    have hrhs : ∏ d, localBlockMass A N (B d) (z d) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      simp [localBlockMass, hd]
    rw [hlhs, hrhs]

private lemma localBlockMass_eq_parameterBlockProductMass {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ) :
    localBlockMass A N B z = parameterBlockProductMass A N B hX z := by
  classical
  let B1 : Fin 1 → OAI.SourceBlocks.Block n := fun _ => B
  let z1 : Fin 1 → ℤ := fun _ => z
  have hdisj1 : ∀ i j, i ≠ j → Disjoint (B1 i).set (B1 j).set := by
    intro i j hij
    have hEq : i = j := Subsingleton.elim _ _
    exact (hij hEq).elim
  have hfactor := parameterJointBlockProductMass_eq_localBlockMass_product
    A N B1 hX hdisj1 z1
  have hmassEq : parameterJointBlockProductMass A N B1 hX z1 =
      parameterBlockProductMass A N B hX z := by
    unfold parameterJointBlockProductMass parameterBlockProductMass
    by_cases hz : 0 ≤ z <;> simp [B1, z1, hz]
  calc
    localBlockMass A N B z =
        ∏ d : Fin 1, localBlockMass A N (B1 d) (z1 d) := by simp [B1, z1]
    _ = parameterJointBlockProductMass A N B1 hX z1 := hfactor.symm
    _ = parameterBlockProductMass A N B hX z := hmassEq

private lemma parameterTailProductLaw_finset {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (σ : ℕ) :
    parameterTailProductLaw A N T σ =
      ∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
        if (∏ j ∈ T, t j) = σ then
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) else 0 := by
  classical
  unfold parameterTailProductLaw
  let D := OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
  rw [tsum_eq_sum (s := D)]
  · apply Finset.sum_congr rfl
    intro t ht
    by_cases hprod : (∏ j ∈ T, t j) = σ <;> simp [hprod]
  · intro t ht
    have hnot : ¬ ∀ j, t j ∈
        OAI.RawHarmonicProbability.units (A.X N j) (primorial (N + 1)) := by
      simpa [D, OAI.ProductExposureLaw.outsideDomain] using ht
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero : harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
      unfold harmonicNatLaw
      split_ifs with h
      · exfalso
        have hunit : t j ∈ OAI.RawHarmonicProbability.units (A.X N j) (primorial (N + 1)) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2.symm⟩
        exact hj hunit
      · rfl
    have hprod : (∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact hzero
    simp [hzero, hprod]

private abbrev PivotRest {ι : Type*} (i : ι) := {j : ι // j ≠ i}

private def piSplitEquiv {ι α : Type*} [DecidableEq ι] (i : ι) :
    (ι → α) ≃ α × (PivotRest i → α) where
  toFun x := (x i, fun j => x j.val)
  invFun p j := if h : j = i then p.1 else p.2 ⟨j, h⟩
  left_inv x := by
    funext j
    dsimp
    split_ifs with h
    · simpa [h]
    · rfl
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      dsimp
      simp [j.property]

private def pivotRestEraseEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    PivotRest i ≃ {j : ι // j ∈ Finset.univ.erase i} where
  toFun j := ⟨j.val, Finset.mem_erase.mpr ⟨j.property, Finset.mem_univ _⟩⟩
  invFun j := ⟨j.val, (Finset.mem_erase.mp j.property).1⟩
  left_inv j := by apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; rfl

private lemma piSplit_product {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : ι → α → ℝ) (a : α) (r : PivotRest i → α) :
    (∏ j, f j ((piSplitEquiv i).symm (a, r) j)) =
      f i a * ∏ j : PivotRest i, f j.val (r j) := by
  classical
  let x : ι → α := (piSplitEquiv i).symm (a, r)
  have hrest :
      (∏ j ∈ Finset.univ.erase i, f j (x j)) =
        ∏ j : PivotRest i, f j.val (r j) := by
    rw [← Finset.prod_coe_sort (Finset.univ.erase i) (fun j => f j (x j))]
    have h := Fintype.prod_equiv (pivotRestEraseEquiv i)
      (fun j : PivotRest i => f j.val (r j))
      (fun j : {j : ι // j ∈ Finset.univ.erase i} => f j.val (x j.val))
      (by intro j; simp [x, piSplitEquiv, pivotRestEraseEquiv, j.property])
    simpa using h.symm
  have hfull := Finset.prod_erase_mul (s := (Finset.univ : Finset ι))
    (f := fun j => f j (x j)) (a := i) (Finset.mem_univ i)
  calc
    _ = (∏ j ∈ Finset.univ.erase i, f j (x j)) * f i (x i) := hfull.symm
    _ = (∏ j : PivotRest i, f j.val (r j)) * f i a := by
      rw [hrest]
      have hxi : x i = a := by simp [x, piSplitEquiv]
      rw [hxi]
    _ = f i a * ∏ j : PivotRest i, f j.val (r j) := by ring

private theorem finite_pi_sum_split {ι α : Type*} [Fintype ι]
    [DecidableEq ι] (U : ι → Finset α) (i : ι) (f : ι → α → ℝ)
    (G : (PivotRest i → α) → ℝ) :
    (∑ x ∈ Fintype.piFinset U,
      (∏ j, f j (x j)) * G (fun j => x j.val)) =
      (∑ a ∈ U i, f i a) *
        ∑ r ∈ Fintype.piFinset (fun j : PivotRest i => U j.val),
          (∏ j : PivotRest i, f j.val (r j)) * G (fun j => r j) := by
  classical
  let R : Finset (PivotRest i → α) := Fintype.piFinset (fun j : PivotRest i => U j.val)
  let D : Finset (ι → α) := Fintype.piFinset U
  let E : {x : ι → α // x ∈ D} ≃
      {a : α // a ∈ U i} × {r : PivotRest i → α // r ∈ R} := {
    toFun := fun (x : {x : ι → α // x ∈ D}) =>
      (⟨x.1 i, (Fintype.mem_piFinset.mp x.2) i⟩,
        ⟨fun j => x.1 j.val, by
          apply Fintype.mem_piFinset.mpr
          intro j
          exact (Fintype.mem_piFinset.mp x.2) j.val⟩)
    invFun := fun p =>
      ⟨(piSplitEquiv i).symm (p.1.1, p.2.1), by
        apply Fintype.mem_piFinset.mpr
        intro j
        by_cases h : j = i
        · subst j
          simpa [piSplitEquiv] using p.1.2
        · change ((piSplitEquiv i).symm (p.1.1, p.2.1)) j ∈ U j
          simpa [piSplitEquiv, h] using (Fintype.mem_piFinset.mp p.2.2) ⟨j, h⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext j
      by_cases h : j = i
      · subst j
        simp [piSplitEquiv]
      · simp [piSplitEquiv, h]
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        simp [piSplitEquiv]
      · apply Subtype.ext
        funext j
        simp [piSplitEquiv, j.property]
  }
  have hsum :
      (∑ x : {x : ι → α // x ∈ D},
        (∏ j, f j (x.1 j)) * G (fun j => x.1 j.val)) =
      ∑ p : {a : α // a ∈ U i} × {r : PivotRest i → α // r ∈ R},
        (∏ j, f j ((piSplitEquiv i).symm (p.1.1, p.2.1) j)) *
          G (fun j => (piSplitEquiv i).symm (p.1.1, p.2.1) j.val) := by
    apply Fintype.sum_equiv E
    intro x
    apply congrArg (fun y : (ι → α) => (∏ j, f j (y j)) * G (fun j => y j.val))
    exact congrArg Subtype.val (E.left_inv x).symm
  have hrestFun (a : α) (r : PivotRest i → α) :
      (fun j : PivotRest i => (piSplitEquiv i).symm (a, r) j.val) = r := by
    funext j
    simp [piSplitEquiv, j.property]
  rw [← Finset.sum_coe_sort D (fun x => (∏ j, f j (x j)) * G (fun j => x j.val))]
  rw [← Finset.sum_coe_sort (U i) (fun a => f i a)]
  rw [← Finset.sum_coe_sort R
    (fun r => (∏ j : PivotRest i, f j.val (r j)) * G (fun j => r j))]
  rw [hsum, Fintype.sum_prod_type]
  dsimp only
  simp_rw [piSplit_product, hrestFun]
  have hcoe :
      (∑ a : {a : α // a ∈ U i},
        ∑ r : {r : PivotRest i → α // r ∈ R},
          (f i a.1 * ∏ j : PivotRest i, f j.val (r.1 j)) * G r.1) =
      ∑ a ∈ U i, ∑ r ∈ R,
        (f i a * ∏ j : PivotRest i, f j.val (r j)) * G r := by
    calc
      _ = ∑ a ∈ U i,
            ∑ r : {r : PivotRest i → α // r ∈ R},
              (f i a * ∏ j : PivotRest i, f j.val (r.1 j)) * G r.1 :=
            Finset.sum_coe_sort (U i) (fun a : α =>
              ∑ r : {r : PivotRest i → α // r ∈ R},
                (f i a * ∏ j : PivotRest i, f j.val (r.1 j)) * G r.1)
      _ = ∑ a ∈ U i, ∑ r ∈ R,
            (f i a * ∏ j : PivotRest i, f j.val (r j)) * G r := by
            apply Finset.sum_congr rfl
            intro a ha
            exact Finset.sum_coe_sort R
              (fun r : PivotRest i → α =>
                (f i a * ∏ j : PivotRest i, f j.val (r j)) * G r)
  rw [hcoe]
  rw [Finset.sum_coe_sort (s := U i)]
  rw [Finset.sum_coe_sort R
    (fun r : PivotRest i → α =>
      (∏ j : PivotRest i, f j.val (r j)) * G r)]
  calc
    _ = ∑ a ∈ U i,
          f i a * ∑ r ∈ R,
            (∏ j : PivotRest i, f j.val (r j)) * G r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = (∑ a ∈ U i, f i a) *
          ∑ r ∈ R, (∏ j : PivotRest i, f j.val (r j)) * G r := by
          rw [Finset.sum_mul]

private theorem finite_pi_sum_split_general {ι α : Type*} [Fintype ι]
    [DecidableEq ι] (U : ι → Finset α) (i : ι) (F : (ι → α) → ℝ) :
    (∑ x ∈ Fintype.piFinset U, F x) =
      ∑ a ∈ U i, ∑ r ∈ Fintype.piFinset (fun j : PivotRest i => U j.val),
        F ((piSplitEquiv i).symm (a, fun j => r j)) := by
  classical
  let R : Finset (PivotRest i → α) := Fintype.piFinset (fun j : PivotRest i => U j.val)
  let D : Finset (ι → α) := Fintype.piFinset U
  let E : {x : ι → α // x ∈ D} ≃
      {a : α // a ∈ U i} × {r : PivotRest i → α // r ∈ R} := {
    toFun := fun (x : {x : ι → α // x ∈ D}) =>
      (⟨x.1 i, (Fintype.mem_piFinset.mp x.2) i⟩,
        ⟨fun j => x.1 j.val, by
          apply Fintype.mem_piFinset.mpr
          intro j
          exact (Fintype.mem_piFinset.mp x.2) j.val⟩)
    invFun := fun p =>
      ⟨(piSplitEquiv i).symm (p.1.1, p.2.1), by
        apply Fintype.mem_piFinset.mpr
        intro j
        by_cases h : j = i
        · subst j
          simpa [piSplitEquiv] using p.1.2
        · change ((piSplitEquiv i).symm (p.1.1, p.2.1)) j ∈ U j
          simpa [piSplitEquiv, h] using (Fintype.mem_piFinset.mp p.2.2) ⟨j, h⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext j
      by_cases h : j = i
      · subst j
        simp [piSplitEquiv]
      · simp [piSplitEquiv, h]
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        simp [piSplitEquiv]
      · apply Subtype.ext
        funext j
        simp [piSplitEquiv, j.property]
  }
  have hsum :
      (∑ x : {x : ι → α // x ∈ D}, F x.1) =
        ∑ p : {a : α // a ∈ U i} × {r : PivotRest i → α // r ∈ R},
          F ((piSplitEquiv i).symm (p.1.1, p.2.1)) := by
    apply Fintype.sum_equiv E
    intro x
    apply congrArg F
    exact congrArg Subtype.val (E.left_inv x).symm
  calc
    (∑ x ∈ D, F x) = ∑ x : {x : ι → α // x ∈ D}, F x.1 :=
      (Finset.sum_coe_sort D (fun x => F x)).symm
    _ = ∑ p : {a : α // a ∈ U i} × {r : PivotRest i → α // r ∈ R},
          F ((piSplitEquiv i).symm (p.1.1, p.2.1)) := hsum
    _ = ∑ a ∈ U i, ∑ r ∈ R, F ((piSplitEquiv i).symm (a, fun j => r j)) := by
          rw [Fintype.sum_prod_type]
          dsimp only
          calc
            _ = ∑ a ∈ U i, ∑ r : {r : PivotRest i → α // r ∈ R},
                  F ((piSplitEquiv i).symm (a, r.1)) :=
                    Finset.sum_coe_sort (U i) (fun a : α =>
                      ∑ r : {r : PivotRest i → α // r ∈ R},
                        F ((piSplitEquiv i).symm (a, r.1)))
            _ = ∑ a ∈ U i, ∑ r ∈ R,
                  F ((piSplitEquiv i).symm (a, fun j => r j)) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    exact Finset.sum_coe_sort R
                      (fun r : PivotRest i → α => F ((piSplitEquiv i).symm (a, r)))

private lemma harmonicNatLaw_sum_units (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) :
    ∑ m ∈ OAI.RawHarmonicProbability.units X W, harmonicNatLaw X W m = 1 := by
  classical
  let μ : Measure ℕ := OAI.RawHarmonicProbability.law X W hW hX
  have hmass : μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) = 1 := by
    have hEq : μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) = μ.real Set.univ := by
      apply measureReal_congr
      filter_upwards [OAI.ProductExposureLabels.law_ae_units X W hW hX] with m hm
      simp [hm]
    rw [hEq]
    simp [μ]
  calc
    _ = ∑ m ∈ OAI.RawHarmonicProbability.units X W, μ.real {m} := by
      apply Finset.sum_congr rfl
      intro m hm
      exact harmonicNatLaw_eq_singleton_mass X W hW hX m
    _ = μ.real (OAI.RawHarmonicProbability.units X W : Set ℕ) := by
      rw [sum_measureReal_singleton]
    _ = 1 := hmass

private lemma parameterTailProductLaw_pivot_independent {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (i : Fin n) (hi : i ∉ T)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (σ : ℕ) :
    parameterTailProductLaw A N T σ =
      ∑ r ∈ Fintype.piFinset
          (fun j : PivotRest i => OAI.RawHarmonicProbability.units
            (A.X N j.val) (primorial (N + 1))),
        if (∏ j : T, r ⟨j.val, by
              intro heq
              exact hi (by simpa [heq] using j.property)⟩) = σ then
          ∏ j : PivotRest i,
            harmonicNatLaw (A.X N j.val) (primorial (N + 1)) (r j) else 0 := by
  classical
  let U : Fin n → Finset ℕ := fun j =>
    OAI.RawHarmonicProbability.units (A.X N j) (primorial (N + 1))
  let f : Fin n → ℕ → ℝ := fun j m =>
    harmonicNatLaw (A.X N j) (primorial (N + 1)) m
  let G : (PivotRest i → ℕ) → ℝ := fun r =>
    if (∏ j : T, r ⟨j.val, by
          intro hji
          exact hi (by simpa [hji] using j.property)⟩) = σ then 1 else 0
  have hsum := finite_pi_sum_split U i f G
  have hG (t : Fin n → ℕ) :
      G (fun j => t j.val) = if (∏ j ∈ T, t j) = σ then 1 else 0 := by
    unfold G
    exact congrArg (fun x : ℕ => if x = σ then (1 : ℝ) else 0)
      (Finset.prod_coe_sort T (fun j => t j))
  rw [parameterTailProductLaw_finset]
  calc
    _ = (∑ t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)),
          (∏ j, f j (t j)) * G (fun j => t j.val)) := by
          rw [show OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) =
            Fintype.piFinset U by rfl]
          apply Finset.sum_congr rfl
          intro t ht
          rw [hG t]
          simp [f]
    _ = (∑ a ∈ U i, f i a) *
          ∑ r ∈ Fintype.piFinset (fun j : PivotRest i => U j.val),
            (∏ j : PivotRest i, f j.val (r j)) * G r := hsum
    _ = ∑ r ∈ Fintype.piFinset (fun j : PivotRest i => U j.val),
          (∏ j : PivotRest i, f j.val (r j)) * G r := by
          rw [harmonicNatLaw_sum_units (A.X N i) (primorial (N + 1))
            (primorial_pos _) (hX i)]
          ring
    _ = ∑ r ∈ Fintype.piFinset
          (fun j : PivotRest i => OAI.RawHarmonicProbability.units
            (A.X N j.val) (primorial (N + 1))),
          if (∏ j : T, r ⟨j.val, by
                intro hji
                exact hi (by simpa [hji] using j.property)⟩) = σ then
            ∏ j : PivotRest i,
              harmonicNatLaw (A.X N j.val) (primorial (N + 1)) (r j) else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          let P : ℕ := ∏ j : T, r ⟨j.val, by
            intro hji
            exact hi (by simpa [hji] using j.property)⟩
          change (∏ j : PivotRest i, harmonicNatLaw (A.X N j.val)
              (primorial (N + 1)) (r j)) * (if P = σ then 1 else 0) =
            if P = σ then ∏ j : PivotRest i, harmonicNatLaw (A.X N j.val)
              (primorial (N + 1)) (r j) else 0
          by_cases hp : P = σ <;> simp [hp]

private def blockTailProductOnRest {n : ℕ} (B : OAI.SourceBlocks.Block n)
    (r : PivotRest B.1 → ℕ) : ℕ :=
  ∏ j : B.2.val, r ⟨j.val, ne_of_lt (B.2.property.2 j.val j.property)⟩

private lemma parameterBlockProductMass_pivot_split {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ) (hz : 0 ≤ z) :
    parameterBlockProductMass A N B hX z =
      ∑ r ∈ Fintype.piFinset
          (fun j : PivotRest B.1 => OAI.RawHarmonicProbability.units
            (A.X N j.val) (primorial (N + 1))),
        ∑ a ∈ OAI.RawHarmonicProbability.units (A.X N B.1) (primorial (N + 1)),
          if (blockTailProductOnRest B r * a) = z.toNat then
            harmonicNatLaw (A.X N B.1) (primorial (N + 1)) a *
              (∏ j : PivotRest B.1,
                harmonicNatLaw (A.X N j.val) (primorial (N + 1)) (r j)) else 0 := by
  classical
  let W := primorial (N + 1)
  let U : Fin n → Finset ℕ := fun j =>
    OAI.RawHarmonicProbability.units (A.X N j) W
  let f : Fin n → ℕ → ℝ := fun j m => harmonicNatLaw (A.X N j) W m
  have hiT : B.1 ∉ B.2.val := by
    intro hmem
    exact (lt_irrefl B.1) (B.2.property.2 B.1 hmem)
  have hdom : OAI.ProductExposureLaw.outsideDomain (A.X N) W =
      Fintype.piFinset U := rfl
  rw [parameterBlockProductMass_finset, if_pos hz, hdom]
  let F : (Fin n → ℕ) → ℝ := fun t =>
    if (∏ j ∈ B.set, t j) = z.toNat then ∏ j, f j (t j) else 0
  have hrewrite :
      (∑ t ∈ Fintype.piFinset U,
        if (∏ j ∈ B.set, t j) = z.toNat then ∏ j, f j (t j) else 0) =
      ∑ t ∈ Fintype.piFinset U, F t := by rfl
  rw [hrewrite, finite_pi_sum_split_general U B.1 F]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro a ha
  have hblock (r : PivotRest B.1 → ℕ) (a : ℕ) :
      (∏ j ∈ B.set, (piSplitEquiv B.1).symm (a, r) j) =
        blockTailProductOnRest B r * a := by
    rw [OAI.SourceBlocks.Block.set, Finset.prod_insert hiT]
    have htail :
        (∏ j ∈ B.2.val,
          (piSplitEquiv B.1).symm (a, r) j) = blockTailProductOnRest B r := by
      rw [← Finset.prod_coe_sort B.2.val
        (fun j => (piSplitEquiv B.1).symm (a, r) j)]
      unfold blockTailProductOnRest
      apply Finset.prod_congr rfl
      intro j
      have hne : j.val ≠ B.1 := ne_of_lt (B.2.property.2 j.val j.property)
      simp [piSplitEquiv, hne]
    have hpivot : (piSplitEquiv B.1).symm (a, r) B.1 = a := by
      simp [piSplitEquiv]
    rw [htail, hpivot]
    ring
  have hweight (r : PivotRest B.1 → ℕ) (a : ℕ) :
      (∏ j, f j ((piSplitEquiv B.1).symm (a, r) j)) =
        f B.1 a * ∏ j : PivotRest B.1, f j.val (r j) :=
    piSplit_product B.1 f a r
  simp [F, hblock r a, hweight r a, f, W]

private lemma harmonicLaw_natCast (X W m : ℕ) :
    harmonicLaw X W (m : ℤ) = harmonicNatLaw X W m := by
  simp [harmonicLaw, harmonicNatLaw]

private lemma dilatedLaw_eq_pivot_sum (X W σ : ℕ) (z : ℤ)
    (hσ : 0 < σ) (hz : 0 ≤ z) :
    dilatedLaw (harmonicLaw X W) σ z =
      ∑ m ∈ OAI.RawHarmonicProbability.units X W,
        if σ * m = z.toNat then harmonicNatLaw X W m else 0 := by
  classical
  have hzcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hz
  have hdivNat : ((σ : ℤ) ∣ z) ↔ σ ∣ z.toNat := by
    rw [← hzcast]
    exact Int.natCast_dvd_natCast
  have hquot (hdiv : σ ∣ z.toNat) :
      z / (σ : ℤ) = ((z.toNat / σ : ℕ) : ℤ) := by
    rw [← hzcast]
    exact (Int.natCast_ediv z.toNat σ).symm
  have hqmul (hdiv : σ ∣ z.toNat) : σ * (z.toNat / σ) = z.toNat :=
    Nat.mul_div_cancel' hdiv
  by_cases hdiv : σ ∣ z.toNat
  · have hdivI : (σ : ℤ) ∣ z := hdivNat.mpr hdiv
    have hmod : z % (σ : ℤ) = 0 := Int.emod_eq_zero_of_dvd hdivI
    have hq := hquot hdiv
    have hsum :
        (∑ m ∈ OAI.RawHarmonicProbability.units X W,
          if σ * m = z.toNat then harmonicNatLaw X W m else 0) =
        if z.toNat / σ ∈ OAI.RawHarmonicProbability.units X W then
          harmonicNatLaw X W (z.toNat / σ) else 0 := by
      have hcond (m : ℕ) : σ * m = z.toNat ↔ m = z.toNat / σ := by
        constructor
        · intro hm
          apply Nat.mul_left_cancel (by omega : 0 < σ)
          rw [hqmul hdiv]
          exact hm
        · intro hm
          subst m
          exact hqmul hdiv
      simp_rw [hcond]
      rw [Finset.sum_ite_eq']
    have hp0 : harmonicNatLaw X W (z.toNat / σ) =
        if z.toNat / σ ∈ OAI.RawHarmonicProbability.units X W then
          harmonicNatLaw X W (z.toNat / σ) else 0 := by
      by_cases hmem : z.toNat / σ ∈ OAI.RawHarmonicProbability.units X W
      · simp [hmem]
      · unfold harmonicNatLaw
        split_ifs with h
        · exfalso
          apply hmem
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2.symm⟩
        · rfl
    unfold dilatedLaw
    rw [if_pos hmod, hq, harmonicLaw_natCast, hsum]
    exact hp0
  · have hdivI : ¬ (σ : ℤ) ∣ z := by
      intro hd
      exact hdiv (hdivNat.mp hd)
    have hmod : z % (σ : ℤ) ≠ 0 := by
      intro hm
      exact hdivI (Int.dvd_iff_emod_eq_zero.mpr hm)
    have hsum :
        (∑ m ∈ OAI.RawHarmonicProbability.units X W,
          if σ * m = z.toNat then harmonicNatLaw X W m else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hneq : σ * m ≠ z.toNat := by
        intro heq
        apply hdiv
        exact ⟨m, heq.symm⟩
      simp [hneq]
    unfold dilatedLaw
    rw [if_neg hmod, hsum]

private lemma parameterTailProductLaw_mass_one {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (T : Finset (Fin n)) (i : Fin n) (hi : i ∉ T)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) :
    ∑' σ : ℕ, parameterTailProductLaw A N T σ = 1 := by
  classical
  let W := primorial (N + 1)
  let U : Fin n → Finset ℕ := fun j =>
    OAI.RawHarmonicProbability.units (A.X N j) W
  let R : Finset (PivotRest i → ℕ) :=
    Fintype.piFinset (fun j : PivotRest i => U j.val)
  let w (r : PivotRest i → ℕ) : ℝ :=
    ∏ j : PivotRest i, harmonicNatLaw (A.X N j.val) W (r j)
  let P (r : PivotRest i → ℕ) : ℕ :=
    ∏ j : T, r ⟨j.val, by
      intro hji
      exact hi (by simpa [hji] using j.property)⟩
  let S : Finset ℕ := R.image P
  have htail (σ : ℕ) : parameterTailProductLaw A N T σ =
      ∑ r ∈ R, if P r = σ then w r else 0 := by
    simpa [R, U, W, w, P, Finset.prod_coe_sort] using
      parameterTailProductLaw_pivot_independent A N T i hi hX σ
  have hzero {σ : ℕ} (hσ : σ ∉ S) : parameterTailProductLaw A N T σ = 0 := by
    rw [htail σ]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hp : P r = σ
    · exact (hσ (Finset.mem_image.mpr ⟨r, hr, hp⟩)).elim
    · simp [hp]
  have hsum :
      (∑' σ : ℕ, parameterTailProductLaw A N T σ) =
        ∑ σ ∈ S, parameterTailProductLaw A N T σ := by
    exact tsum_eq_sum (s := S) (fun σ hσ => hzero hσ)
  have hcollapse :
      (∑ σ ∈ S, parameterTailProductLaw A N T σ) = ∑ r ∈ R, w r := by
    calc
      _ = ∑ σ ∈ S, ∑ r ∈ R, if P r = σ then w r else 0 := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [htail σ]
      _ = ∑ r ∈ R, ∑ σ ∈ S, if P r = σ then w r else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ r ∈ R, w r := by
            apply Finset.sum_congr rfl
            intro r hr
            have hmem : P r ∈ S := Finset.mem_image.mpr ⟨r, hr, rfl⟩
            rw [Finset.sum_ite_eq]
            simp [hmem]
  have hrest : (∑ r ∈ R, w r) = 1 := by
    let Urest : PivotRest i → Finset ℕ := fun j => U j.val
    let frest : PivotRest i → ℕ → ℝ := fun j a =>
      harmonicNatLaw (A.X N j.val) W a
    rw [show (∑ r ∈ R, w r) =
        ∑ r ∈ Fintype.piFinset Urest, ∏ j : PivotRest i, frest j (r j) by rfl]
    rw [← Finset.prod_univ_sum]
    have hcoord (j : PivotRest i) :
        (∑ a ∈ Urest j, frest j a) = 1 := by
      exact harmonicNatLaw_sum_units (A.X N j.val) W
        (primorial_pos _) (hX j.val)
    simp_rw [hcoord]
    simp
  calc
    _ = ∑ σ ∈ S, parameterTailProductLaw A N T σ := hsum
    _ = ∑ r ∈ R, w r := hcollapse
    _ = 1 := hrest

private lemma arithmeticL1_finite_mixture_bound {σ : Type*} [DecidableEq σ]
    (S : Finset σ) (Z : Finset ℤ) (p : σ → ℝ)
    (μ ν : σ → ℤ → ℝ) (hp : ∀ s ∈ S, 0 ≤ p s)
    (hsupp : ∀ s ∈ S, ∀ z ∉ Z, μ s z = 0 ∧ ν s z = 0) :
    arithmeticL1 (fun z => ∑ s ∈ S, p s * μ s z)
      (fun z => ∑ s ∈ S, p s * ν s z) ≤
        ∑ s ∈ S, p s * arithmeticL1 (μ s) (ν s) := by
  classical
  have hzero (z : ℤ) (hz : z ∉ Z) :
      (∑ s ∈ S, p s * μ s z) - (∑ s ∈ S, p s * ν s z) = 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro s hs
    rcases hsupp s hs z hz with ⟨hμ, hν⟩
    simp [hμ, hν]
  have hL1 (s : σ) (hs : s ∈ S) :
      arithmeticL1 (μ s) (ν s) = ∑ z ∈ Z, |μ s z - ν s z| := by
    unfold arithmeticL1
    exact tsum_eq_sum (s := Z) (fun z hz => by
      rcases hsupp s hs z hz with ⟨hμ, hν⟩
      simp [hμ, hν])
  unfold arithmeticL1
  rw [tsum_eq_sum (s := Z) (fun z hz => by
    rw [hzero z hz]
    simp)]
  · calc
      (∑ z ∈ Z,
          |(∑ s ∈ S, p s * μ s z) - (∑ s ∈ S, p s * ν s z)|) ≤
          ∑ z ∈ Z, ∑ s ∈ S, p s * |μ s z - ν s z| := by
            apply Finset.sum_le_sum
            intro z hz
            have hsum :
                (∑ s ∈ S, p s * μ s z) - (∑ s ∈ S, p s * ν s z) =
                  ∑ s ∈ S, p s * (μ s z - ν s z) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro s hs
              ring
            rw [hsum]
            calc
              _ ≤ ∑ s ∈ S, |p s * (μ s z - ν s z)| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ s ∈ S, p s * |μ s z - ν s z| := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    rw [abs_mul, abs_of_nonneg (hp s hs)]
      _ = ∑ s ∈ S, p s * ∑ z ∈ Z, |μ s z - ν s z| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.mul_sum]
      _ = ∑ s ∈ S, p s * arithmeticL1 (μ s) (ν s) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hL1 s hs]

private lemma dilatedLaw_zero_of_negative (X W k : ℕ) {z : ℤ} (hz : z < 0) :
    dilatedLaw (harmonicLaw X W) k z = 0 := by
  classical
  unfold dilatedLaw
  by_cases hmod : z % (k : ℤ) = 0
  · have hk : k ≠ 0 := by
      intro hk
      subst k
      simp at hmod
      omega
    have hkpos : 0 < (k : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hquot : z / (k : ℤ) < 0 := by
      have hformula : z / (k : ℤ) = -((-z - 1) / (k : ℤ) + 1) :=
        Int.ediv_of_neg_of_pos hz hkpos
      rw [hformula]
      have hnum : 0 ≤ -z - 1 := by omega
      have hnat : (((-z - 1).toNat : ℤ)) = -z - 1 :=
        Int.natCast_toNat_eq_self.mpr hnum
      have hdiv : 0 ≤ (-z - 1) / (k : ℤ) := by
        rw [← hnat, ← Int.natCast_ediv]
        exact_mod_cast (Nat.zero_le (((-z - 1).toNat) / k))
      omega
    simp [hmod, harmonicLaw, not_le_of_gt hquot]
  · simp [hmod]

private lemma parameterBlock_l1_le_dilationError {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j)
    (hPoint : SamplingPointwiseBounds (A.X N B.1) (primorial (N + 1)))
    (hXlarge : 2 ≤ A.X N B.1)
    (hlog : Real.log (A.X N B.1) > (primorial (N + 1) : ℝ) / A.X N B.1)
    (K : ℕ) (hK : 1 ≤ K) (hKX : K ≤ A.X N B.1)
    (hTailPos : ∀ r ∈ Fintype.piFinset
      (fun j : PivotRest B.1 => OAI.RawHarmonicProbability.units
        (A.X N j.val) (primorial (N + 1))), 1 ≤ blockTailProductOnRest B r)
    (hTailLe : ∀ r ∈ Fintype.piFinset
      (fun j : PivotRest B.1 => OAI.RawHarmonicProbability.units
        (A.X N j.val) (primorial (N + 1))), blockTailProductOnRest B r ≤ K)
    (hTailCoprime : ∀ r ∈ Fintype.piFinset
      (fun j : PivotRest B.1 => OAI.RawHarmonicProbability.units
        (A.X N j.val) (primorial (N + 1))),
          Nat.Coprime (blockTailProductOnRest B r) (primorial (N + 1))) :
    arithmeticL1 (parameterBlockProductMass A N B (hX))
      (weightedPivotMass A N B) ≤
        harmonicDilationUniformError (A.X N B.1) (primorial (N + 1)) K := by
  classical
  let W := primorial (N + 1)
  let i := B.1
  let U := OAI.RawHarmonicProbability.units (A.X N i) W
  let R : Finset (PivotRest i → ℕ) :=
    Fintype.piFinset (fun j : PivotRest i =>
      OAI.RawHarmonicProbability.units (A.X N j.val) W)
  let restWeight (r : PivotRest i → ℕ) : ℝ :=
    ∏ j : PivotRest i, harmonicNatLaw (A.X N j.val) W (r j)
  let μ (r : PivotRest i → ℕ) : ℤ → ℝ :=
    dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r)
  let ν (r : PivotRest i → ℕ) : ℤ → ℝ :=
    dilationReference (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r)
  let Z : Finset ℤ := Finset.Icc (0 : ℤ) ((K * (A.X N i) ^ 2 : ℕ) : ℤ)
  have hXpos : 0 < (A.X N i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hXlarge)
  have hdenpos : 0 < Real.log (A.X N i : ℝ) - (W : ℝ) / A.X N i := by linarith
  have hrestSum : ∑ r ∈ R, restWeight r = 1 := by
    let Urest : PivotRest i → Finset ℕ := fun j =>
      OAI.RawHarmonicProbability.units (A.X N j.val) W
    let frest : PivotRest i → ℕ → ℝ := fun j a =>
      harmonicNatLaw (A.X N j.val) W a
    have hsum : (∑ r ∈ R, restWeight r) =
        ∏ j : PivotRest i, ∑ a ∈ Urest j, frest j a := by
      rw [show (∑ r ∈ R, restWeight r) =
          ∑ r ∈ Fintype.piFinset Urest, ∏ j : PivotRest i, frest j (r j) by rfl]
      rw [← Finset.prod_univ_sum]
    rw [hsum]
    have hcoord (j : PivotRest i) : ∑ a ∈ Urest j, frest j a = 1 := by
      exact harmonicNatLaw_sum_units (A.X N j.val) W (primorial_pos _) (hX j.val)
    simp_rw [hcoord]
    simp
  have hrestNonneg : ∀ r ∈ R, 0 ≤ restWeight r := by
    intro r hr
    unfold restWeight
    apply Finset.prod_nonneg
    intro j hj
    have hWpos : 0 < W := by dsimp [W]; exact primorial_pos _
    have hXj : 4 * W ≤ A.X N j.val := by simpa [W] using hX j.val
    rw [harmonicNatLaw_eq_singleton_mass (A.X N j.val) W hWpos hXj (r j)]
    exact measureReal_nonneg
  have hTailLaw (σ : ℕ) : parameterTailProductLaw A N B.2.val σ =
      ∑ r ∈ R, if blockTailProductOnRest B r = σ then restWeight r else 0 := by
    simpa [R, restWeight, W, blockTailProductOnRest, Finset.prod_coe_sort] using
      parameterTailProductLaw_pivot_independent A N B.2.val i (by
        intro hmem
        exact (lt_irrefl i) (B.2.property.2 i hmem)) (hX) σ
  let Sigmas : Finset ℕ := R.image (blockTailProductOnRest B)
  have hTailZero {σ : ℕ} (hσ : σ ∉ Sigmas) :
      parameterTailProductLaw A N B.2.val σ = 0 := by
    rw [hTailLaw σ]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hval : blockTailProductOnRest B r = σ
    · exact (hσ (Finset.mem_image.mpr ⟨r, hr, hval⟩)).elim
    · simp [hval]
  have hactual (z : ℤ) :
      parameterBlockProductMass A N B (hX) z =
        ∑ r ∈ R, restWeight r * μ r z := by
    by_cases hz : 0 ≤ z
    · rw [parameterBlockProductMass_pivot_split A N B (hX) z hz]
      apply Finset.sum_congr rfl
      intro r hr
      have hinner :
          (∑ a ∈ U,
            if blockTailProductOnRest B r * a = z.toNat then
              harmonicNatLaw (A.X N i) W a else 0) = μ r z := by
        simpa [U, μ] using
          (dilatedLaw_eq_pivot_sum (A.X N i) W (blockTailProductOnRest B r) z
            (hTailPos r hr) hz).symm
      calc
        (∑ a ∈ U,
            if blockTailProductOnRest B r * a = z.toNat then
              harmonicNatLaw (A.X N i) W a * restWeight r else 0) =
            restWeight r * ∑ a ∈ U,
              if blockTailProductOnRest B r * a = z.toNat then
                harmonicNatLaw (A.X N i) W a else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases heq : blockTailProductOnRest B r * a = z.toNat <;>
            simp [heq, mul_comm]
        _ = restWeight r * μ r z := by rw [hinner]
    · have hzero : parameterBlockProductMass A N B (hX) z = 0 := by
        rw [parameterBlockProductMass_finset]
        simp [hz]
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      have hμ : μ r z = 0 := by
        change dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z = 0
        exact dilatedLaw_zero_of_negative (A.X N i) W (blockTailProductOnRest B r)
          (lt_of_not_ge hz)
      simp [hμ]
  have href (z : ℤ) : weightedPivotMass A N B z = ∑ r ∈ R, restWeight r * ν r z := by
    unfold weightedPivotMass nuB
    rw [← tsum_mul_right]
    rw [tsum_eq_sum (s := Sigmas)]
    · calc
        _ = ∑ σ ∈ Sigmas,
              (∑ r ∈ R, if blockTailProductOnRest B r = σ then restWeight r else 0) *
                (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                  harmonicLaw (A.X N i) W z := by
                    apply Finset.sum_congr rfl
                    intro σ hσ
                    rw [hTailLaw σ]
        _ = ∑ σ ∈ Sigmas, ∑ r ∈ R,
              (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                  harmonicLaw (A.X N i) W z := by
                    simp_rw [Finset.sum_mul]
        _ = ∑ r ∈ R, ∑ σ ∈ Sigmas,
              (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                  harmonicLaw (A.X N i) W z := by rw [Finset.sum_comm]
        _ = ∑ r ∈ R, restWeight r * ν r z := by
              apply Finset.sum_congr rfl
              intro r hr
              have hs : blockTailProductOnRest B r ∈ Sigmas :=
                Finset.mem_image.mpr ⟨r, hr, rfl⟩
              have hterm (σ : ℕ) :
                  (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                    (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                      harmonicLaw (A.X N i) W z =
                  if blockTailProductOnRest B r = σ then
                    restWeight r * (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                      harmonicLaw (A.X N i) W z else 0 := by
                by_cases heq : blockTailProductOnRest B r = σ <;> simp [heq]
              calc
                _ = ∑ σ ∈ Sigmas, if blockTailProductOnRest B r = σ then
                      restWeight r * (σ : ℝ) * (if (σ : ℤ) ∣ z then 1 else 0) *
                        harmonicLaw (A.X N i) W z else 0 := by
                      apply Finset.sum_congr rfl
                      intro σ hσ
                      exact hterm σ
                _ = restWeight r * ν r z := by
                      rw [Finset.sum_ite_eq]
                      by_cases hdiv :
                          ((blockTailProductOnRest B r : ℕ) : ℤ) ∣ z <;>
                        simp [hs, ν, dilationReference, hdiv] <;> ring
    · intro σ hσ
      simp [hTailZero hσ]
  have hZsupp (r : PivotRest i → ℕ) (hr : r ∈ R) (z : ℤ) (hz : z ∉ Z) :
      μ r z = 0 ∧ ν r z = 0 := by
    have hσpos : 1 ≤ blockTailProductOnRest B r := hTailPos r hr
    have hσle : blockTailProductOnRest B r ≤ K := hTailLe r hr
    have hσcop : Nat.Coprime (blockTailProductOnRest B r) W := hTailCoprime r hr
    constructor
    · by_cases hzpos : 0 ≤ z
      · change dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z = 0
        rw [dilatedLaw_eq_pivot_sum (A.X N i) W (blockTailProductOnRest B r) z
          (by omega) hzpos]
        apply Finset.sum_eq_zero
        intro y hy
        by_cases heq : blockTailProductOnRest B r * y = z.toNat
        · exfalso
          have hyUnit := hy
          have hyupper : y ≤ (A.X N i) ^ 2 := by
            have hmem := Finset.mem_filter.mp hyUnit
            exact Nat.le_of_lt (Finset.mem_Ico.mp hmem.1).2
          have hupper : blockTailProductOnRest B r * y ≤ K * (A.X N i) ^ 2 :=
            Nat.mul_le_mul hσle hyupper
          have hzupper : z ≤ ((K * (A.X N i) ^ 2 : ℕ) : ℤ) := by
            rw [← Int.natCast_toNat_eq_self.mpr hzpos]
            exact_mod_cast heq ▸ hupper
          exact hz (Finset.mem_Icc.mpr ⟨hzpos, hzupper⟩)
        · simp [heq]
      · change dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z = 0
        rw [dilatedLaw_zero_of_negative (A.X N i) W
          (blockTailProductOnRest B r) (lt_of_not_ge hzpos)]
    · unfold ν dilationReference
      by_cases hdiv : ((blockTailProductOnRest B r : ℕ) : ℤ) ∣ z
      · by_cases hμ : harmonicLaw (A.X N i) W z = 0
        · simp [hdiv, hμ]
        · have hzpos : 0 ≤ z := by
            by_contra hn
            simp [harmonicLaw, not_le_of_gt (lt_of_not_ge hn)] at hμ
          have hcond : A.X N i ≤ z.toNat ∧ z.toNat < (A.X N i) ^ 2 ∧
              Nat.Coprime z.toNat W := by
            unfold harmonicLaw at hμ
            by_cases hc : 0 ≤ z ∧ A.X N i ≤ z.toNat ∧
                z.toNat < (A.X N i) ^ 2 ∧ Nat.Coprime z.toNat W
            · exact hc.2
            · simp [hc] at hμ
          have hupperNat : z.toNat ≤ K * (A.X N i) ^ 2 := by
            calc
              z.toNat ≤ (A.X N i) ^ 2 := hcond.2.1.le
              _ ≤ K * (A.X N i) ^ 2 := by
                simpa using Nat.mul_le_mul_right ((A.X N i) ^ 2) hK
          have hupper : z ≤ ((K * (A.X N i) ^ 2 : ℕ) : ℤ) := by
            rw [← Int.natCast_toNat_eq_self.mpr hzpos]
            exact_mod_cast hupperNat
          have hzmem : z ∈ Z := Finset.mem_Icc.mpr ⟨hzpos, hupper⟩
          exact (hz hzmem).elim
      · simp [hdiv]
  have hmix := arithmeticL1_finite_mixture_bound R Z restWeight μ ν
    (fun r hr => hrestNonneg r hr) hZsupp
  have htotal : ∑ r ∈ R, restWeight r = 1 := by
    let Urest : PivotRest i → Finset ℕ := fun j =>
      OAI.RawHarmonicProbability.units (A.X N j.val) W
    let frest : PivotRest i → ℕ → ℝ := fun j a =>
      harmonicNatLaw (A.X N j.val) W a
    rw [show (∑ r ∈ R, restWeight r) =
        ∑ r ∈ Fintype.piFinset Urest, ∏ j : PivotRest i, frest j (r j) by rfl]
    rw [← Finset.prod_univ_sum]
    have hcoord (j : PivotRest i) : ∑ a ∈ Urest j, frest j a = 1 := by
      exact harmonicNatLaw_sum_units (A.X N j.val) W (primorial_pos _) (hX j.val)
    simp_rw [hcoord]
    simp
  have hDilBound (r : PivotRest i → ℕ) (hr : r ∈ R) :
      arithmeticL1 (μ r) (ν r) ≤
        harmonicDilationUniformError (A.X N i) W K := by
    have hsample := hPoint.dilation hXlarge hlog (blockTailProductOnRest B r)
      (hTailPos r hr) ((hTailLe r hr).trans hKX) (hTailCoprime r hr)
    have hlogle : Real.log (blockTailProductOnRest B r : ℝ) ≤ Real.log K :=
      Real.log_le_log (by exact_mod_cast (hTailPos r hr)) (by exact_mod_cast (hTailLe r hr))
    have hmul : (W : ℝ) * (blockTailProductOnRest B r) / A.X N i *
        (1 + 1 / A.X N i) ≤
        (W : ℝ) * K / A.X N i * (1 + 1 / A.X N i) := by
      have hW : (W : ℝ) * (blockTailProductOnRest B r) ≤ (W : ℝ) * K := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hTailLe r hr) (by positivity)
      apply mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hW (by positivity)) (by positivity)
    have hnum : 2 * Real.log (blockTailProductOnRest B r : ℝ) +
        (W : ℝ) * (blockTailProductOnRest B r) / A.X N i *
          (1 + 1 / A.X N i) ≤
        2 * Real.log K + (W : ℝ) * K / A.X N i * (1 + 1 / A.X N i) :=
      add_le_add (mul_le_mul_of_nonneg_left hlogle (by norm_num)) hmul
    exact hsample.1.trans (div_le_div_of_nonneg_right hnum (by positivity))
  have hupper : ∑ r ∈ R, restWeight r * arithmeticL1 (μ r) (ν r) ≤
      harmonicDilationUniformError (A.X N i) W K := by
    calc
      _ ≤ ∑ r ∈ R, restWeight r * harmonicDilationUniformError (A.X N i) W K :=
        Finset.sum_le_sum fun r hr =>
          mul_le_mul_of_nonneg_left (hDilBound r hr) (hrestNonneg r hr)
      _ = harmonicDilationUniformError (A.X N i) W K := by
        rw [← Finset.sum_mul, htotal, one_mul]
  rw [show parameterBlockProductMass A N B (hX) =
      fun z => ∑ r ∈ R, restWeight r * μ r z by funext z; exact hactual z]
  rw [show weightedPivotMass A N B =
      fun z => ∑ r ∈ R, restWeight r * ν r z by funext z; exact href z]
  exact hmix.trans hupper

private lemma dominates_nat_of_log_dominates_scale {X : ℕ → ℕ} {S T : ℕ → ℝ}
    (hS : ∀ N, 1 ≤ S N) (hTpos : ∀ N, 0 < T N)
    (hTle : ∀ N, T N ≤ 2 * S N)
    (hlog : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ)) S) :
    OAI.MicrocellScale.Dominates (fun N => (X N : ℝ)) T := by
  intro C hC
  have hLog := hlog C hC
  have hLow := hLog.atTop_div_const (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) C)
  apply tendsto_atTop_mono' atTop _ hLow
  filter_upwards [hLog.eventually_gt_atTop 0] with N hN
  have hSpos : 0 < S N := by linarith [hS N]
  have hTposN : 0 < T N := hTpos N
  have hSexp : 0 < (S N) ^ C := Real.rpow_pos_of_pos hSpos C
  have hTexp : 0 < (T N) ^ C := Real.rpow_pos_of_pos hTposN C
  have hConst : 0 < (2 : ℝ) ^ C := Real.rpow_pos_of_pos (by norm_num) C
  have hLogPos : 0 < Real.log (X N : ℝ) := by
    rcases (div_pos_iff.mp hN) with hpos | hneg
    · exact hpos.1
    · linarith [hSexp, hneg.2]
  have hpow : (T N) ^ C ≤ (2 : ℝ) ^ C * (S N) ^ C := by
    calc
      (T N) ^ C ≤ (2 * S N) ^ C := Real.rpow_le_rpow (by positivity) (hTle N) hC.le
      _ = _ := by rw [Real.mul_rpow (by norm_num) hSpos.le]
  have hbigpos : 0 < (2 : ℝ) ^ C * (S N) ^ C := mul_pos hConst hSexp
  have hcross : Real.log (X N : ℝ) * (T N) ^ C ≤
      (X N : ℝ) * ((2 : ℝ) ^ C * (S N) ^ C) := by
    calc
      _ ≤ Real.log (X N : ℝ) * ((2 : ℝ) ^ C * (S N) ^ C) :=
        mul_le_mul_of_nonneg_left hpow hLogPos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.log_le_self (by positivity)) hbigpos.le
  calc
    ((Real.log (X N : ℝ) / (S N) ^ C) / (2 : ℝ) ^ C) =
        Real.log (X N : ℝ) / ((2 : ℝ) ^ C * (S N) ^ C) := by ring
    _ ≤ (X N : ℝ) / (T N) ^ C :=
      (div_le_div_iff₀ hbigpos hTexp).2 hcross

private lemma arithmeticL1_pi_product_eq_finiteL1
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Finset ℤ)
    (μ ν : ι → ℤ → ℝ)
    (hμ : ∀ i z, z ∉ Z → μ i z = 0)
    (hν : ∀ i z, z ∉ Z → ν i z = 0) :
    arithmeticL1 (fun z : ι → ℤ => ∏ i, μ i (z i))
        (fun z => ∏ i, ν i (z i)) =
      finiteL1
        (fun x : ι → {z : ℤ // z ∈ Z} => ∏ i, μ i (x i).val)
        (fun x => ∏ i, ν i (x i).val) := by
  classical
  let S : Finset (ι → ℤ) := Fintype.piFinset (fun _ : ι => Z)
  have hzero (z : ι → ℤ) (hz : z ∉ S) :
      |(∏ i, μ i (z i)) - (∏ i, ν i (z i))| = 0 := by
    have hnot : ∃ i, z i ∉ Z := by
      by_contra h
      push_neg at h
      exact hz (Fintype.mem_piFinset.mpr h)
    obtain ⟨i, hi⟩ := hnot
    have hμzero : (∏ j, μ j (z j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hμ i (z i) hi
    have hνzero : (∏ j, ν j (z j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hν i (z i) hi
    simp [hμzero, hνzero]
  let e : (ι → {z : ℤ // z ∈ Z}) ≃ {z : ι → ℤ // z ∈ S} := {
    toFun := fun x => ⟨(fun i => (x i).val),
      (show (fun i => (x i).val) ∈ S from
        Fintype.mem_piFinset.mpr (fun i => (x i).property))⟩
    invFun := fun z i => ⟨z.val i, Fintype.mem_piFinset.mp z.property i⟩
    left_inv := by
      intro x
      funext i
      apply Subtype.ext
      rfl
    right_inv := by
      intro z
      apply Subtype.ext
      funext i
      rfl }
  have hsum :
      (∑ x : ι → {z : ℤ // z ∈ Z},
        |(∏ i, μ i (x i).val) - (∏ i, ν i (x i).val)|) =
      ∑ z : {z : ι → ℤ // z ∈ S},
        |(∏ i, μ i (z.val i)) - (∏ i, ν i (z.val i))| := by
    apply Fintype.sum_equiv e
    intro x
    simp [e]
  unfold arithmeticL1
  rw [tsum_eq_sum (s := S) (fun z hz => hzero z hz)]
  unfold finiteL1
  calc
    (∑ z ∈ S, |(∏ i, μ i (z i)) - (∏ i, ν i (z i))|) =
        ∑ z : {z : ι → ℤ // z ∈ S},
          |(∏ i, μ i (z.val i)) - (∏ i, ν i (z.val i))| := by
      rw [← Finset.sum_attach S
        (fun z : ι → ℤ => |(∏ i, μ i (z i)) - (∏ i, ν i (z i))|)]
      rw [Finset.sum_coe_sort_eq_attach]
    _ = ∑ x : ι → {z : ℤ // z ∈ Z},
          |(∏ i, μ i (x i).val) - (∏ i, ν i (x i).val)| := hsum.symm

private def parameterGlobalProductCutoff {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) : ℕ :=
  ∏ j, (A.X N j)^2

private lemma blockProduct_le_globalCutoff {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n) (t : Fin n → ℕ)
    (ht : ∀ j, t j ≤ (A.X N j)^2)
    (hone : ∀ j, 1 ≤ (A.X N j)^2) :
    (∏ j ∈ B.set, t j) ≤ parameterGlobalProductCutoff A N := by
  calc
    (∏ j ∈ B.set, t j) ≤ ∏ j ∈ B.set, (A.X N j)^2 :=
      Finset.prod_le_prod fun j hj => ht j
    _ ≤ ∏ j : Fin n, (A.X N j)^2 :=
      Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
        (fun j hj hnot => hone j)
    _ = parameterGlobalProductCutoff A N := rfl

private lemma parameterBlockProductMass_zero_outside_globalCutoff {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ)
    (hz : z ∉ Finset.Icc (0 : ℤ) (parameterGlobalProductCutoff A N : ℤ)) :
    parameterBlockProductMass A N B hX z = 0 := by
  classical
  by_cases hzneg : z < 0
  · unfold parameterBlockProductMass
    simp [not_le_of_gt hzneg]
  · have hzpos : 0 ≤ z := le_of_not_gt hzneg
    have hnotupper : ¬ z ≤ (parameterGlobalProductCutoff A N : ℤ) := by
      intro hzle
      exact hz (Finset.mem_Icc.mpr ⟨hzpos, hzle⟩)
    rw [parameterBlockProductMass_finset]
    simp only [if_pos hzpos]
    let W := primorial (N + 1)
    let U : Fin n → Finset ℕ := fun j =>
      OAI.RawHarmonicProbability.units (A.X N j) W
    have hdom : OAI.ProductExposureLaw.outsideDomain (A.X N) W =
        Fintype.piFinset U := rfl
    rw [hdom]
    apply Finset.sum_eq_zero
    intro t ht
    by_cases heq : (∏ j ∈ B.set, t j) = z.toNat
    · have hone : ∀ j, 1 ≤ (A.X N j)^2 := by
        intro j
        have hw : 1 ≤ primorial (N + 1) :=
          Nat.one_le_iff_ne_zero.mpr (primorial_pos _).ne'
        have hxi : 1 ≤ A.X N j := by nlinarith [hX j]
        exact Nat.one_le_pow _ _ hxi
      have htbound : ∀ j, t j ≤ (A.X N j)^2 := by
        intro j
        have hu := Fintype.mem_piFinset.mp ht j
        rcases Finset.mem_filter.mp hu with ⟨hI, _⟩
        exact Nat.le_of_lt (Finset.mem_Ico.mp hI).2
      have hprod := blockProduct_le_globalCutoff A N B t htbound hone
      have hzNat : z.toNat ≤ parameterGlobalProductCutoff A N := by
        rw [← heq]
        exact hprod
      have hzle : z ≤ (parameterGlobalProductCutoff A N : ℤ) := by
        rw [← Int.natCast_toNat_eq_self.mpr hzpos]
        exact_mod_cast hzNat
      exact (hnotupper hzle).elim
    · simp [heq]

private lemma parameterBlockProductMass_sum_globalCutoff {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) :
    (∑ z ∈ Finset.Icc (0 : ℤ) (parameterGlobalProductCutoff A N : ℤ),
      parameterBlockProductMass A N B hX z) = 1 := by
  classical
  let Z : Finset ℤ := Finset.Icc (0 : ℤ) (parameterGlobalProductCutoff A N : ℤ)
  let W := primorial (N + 1)
  let U : Fin n → Finset ℕ := fun j =>
    OAI.RawHarmonicProbability.units (A.X N j) W
  let D := OAI.ProductExposureLaw.outsideDomain (A.X N) W
  have hD : D = Fintype.piFinset U := rfl
  have hD0 : OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) = D := rfl
  have hone : ∀ j, 1 ≤ (A.X N j)^2 := by
    intro j
    have hw : 1 ≤ primorial (N + 1) :=
      Nat.one_le_iff_ne_zero.mpr (primorial_pos _).ne'
    have hxi : 1 ≤ A.X N j := by nlinarith [hX j]
    exact Nat.one_le_pow _ _ hxi
  have htbound (t : Fin n → ℕ) (ht : t ∈ D) :
      (∏ j ∈ B.set, t j) ≤ parameterGlobalProductCutoff A N := by
    rw [hD] at ht
    have hu : ∀ j, t j ≤ (A.X N j)^2 := by
      intro j
      have hm := Fintype.mem_piFinset.mp ht j
      rcases Finset.mem_filter.mp hm with ⟨hI, _⟩
      exact Nat.le_of_lt (Finset.mem_Ico.mp hI).2
    exact blockProduct_le_globalCutoff A N B t hu hone
  have hrawGlobal :
      (∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) W (t j)) = 1 := by
    have hraw :
        (∑ t ∈ Fintype.piFinset U, ∏ j, harmonicNatLaw (A.X N j) W (t j)) = 1 := by
      rw [← Finset.prod_univ_sum]
      have hcoord (j : Fin n) :
          (∑ a ∈ U j, harmonicNatLaw (A.X N j) W a) = 1 :=
        harmonicNatLaw_sum_units (A.X N j) W (primorial_pos _) (hX j)
      calc
        _ = ∏ j : Fin n, (1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hcoord j
        _ = 1 := by simp
    simpa [hD] using hraw
  have hgrouped :
      (∑ z ∈ Z, parameterBlockProductMass A N B hX z) =
        ∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) W (t j) := by
    calc
      _ = ∑ z ∈ Z, ∑ t ∈ D,
            if (∏ j ∈ B.set, t j) = z.toNat then
              ∏ j, harmonicNatLaw (A.X N j) W (t j) else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzpos : 0 ≤ z := (Finset.mem_Icc.mp hz).1
        rw [parameterBlockProductMass_finset]
        simp only [if_pos hzpos]
        rw [hD0]
      _ = ∑ t ∈ D, ∑ z ∈ Z,
            if (∏ j ∈ B.set, t j) = z.toNat then
              ∏ j, harmonicNatLaw (A.X N j) W (t j) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) W (t j) := by
        apply Finset.sum_congr rfl
        intro t ht
        let P := ∏ j ∈ B.set, t j
        have hPmem : (P : ℤ) ∈ Z := by
          apply Finset.mem_Icc.mpr
          constructor
          · exact Int.natCast_nonneg _
          · exact_mod_cast htbound t ht
        have hconvert :
            (∑ z ∈ Z, if P = z.toNat then
                ∏ j, harmonicNatLaw (A.X N j) W (t j) else 0) =
              ∑ z ∈ Z, if (P : ℤ) = z then
                ∏ j, harmonicNatLaw (A.X N j) W (t j) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          have hzpos : 0 ≤ z := (Finset.mem_Icc.mp hz).1
          have hcast : (z.toNat : ℤ) = z := Int.natCast_toNat_eq_self.mpr hzpos
          have hequiv : P = z.toNat ↔ (P : ℤ) = z := by
            constructor
            · intro heq
              rw [← hcast]
              exact_mod_cast heq
            · intro heq
              have heq' : (P : ℤ) = (z.toNat : ℤ) := by simpa [hcast] using heq
              exact_mod_cast heq'
          exact if_congr hequiv rfl rfl
        rw [hconvert, Finset.sum_ite_eq]
        simp [hPmem]
  have hsum := hgrouped.trans hrawGlobal
  simpa [Z] using hsum

private lemma weightedPivotMass_zero_outside_globalCutoff {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) (z : ℤ)
    (hz : z ∉ Finset.Icc (0 : ℤ) (parameterGlobalProductCutoff A N : ℤ)) :
    weightedPivotMass A N B z = 0 := by
  classical
  by_cases hzneg : z < 0
  · unfold weightedPivotMass
    simp [harmonicLaw, not_le_of_gt hzneg]
  · have hzpos : 0 ≤ z := le_of_not_gt hzneg
    have hnotupper : ¬ z ≤ (parameterGlobalProductCutoff A N : ℤ) := by
      intro hzle
      exact hz (Finset.mem_Icc.mpr ⟨hzpos, hzle⟩)
    have hone : ∀ j, 1 ≤ (A.X N j)^2 := by
      intro j
      have hw : 1 ≤ primorial (N + 1) :=
        Nat.one_le_iff_ne_zero.mpr (primorial_pos _).ne'
      have hxi : 1 ≤ A.X N j := by nlinarith [hX j]
      exact Nat.one_le_pow _ _ hxi
    have hpivot : (A.X N B.1)^2 ≤ parameterGlobalProductCutoff A N :=
      Finset.single_le_prod (fun j hj => hone j) (Finset.mem_univ B.1)
    have hzero : harmonicLaw (A.X N B.1) (primorial (N + 1)) z = 0 := by
      unfold harmonicLaw
      split_ifs with h
      · exfalso
        have hzNat : z.toNat ≤ parameterGlobalProductCutoff A N := by
          have hlt : z.toNat < (A.X N B.1)^2 := h.2.2.1
          exact (Nat.le_of_lt hlt).trans hpivot
        have hzle : z ≤ (parameterGlobalProductCutoff A N : ℤ) := by
          rw [← Int.natCast_toNat_eq_self.mpr hzpos]
          exact_mod_cast hzNat
        exact hnotupper hzle
      · rfl
    unfold weightedPivotMass
    simp [hzero]

private lemma arithmeticL1_eq_finiteL1_of_support (Z : Finset ℤ)
    (μ ν : ℤ → ℝ) (hμ : ∀ z ∉ Z, μ z = 0) (hν : ∀ z ∉ Z, ν z = 0) :
    arithmeticL1 μ ν =
      finiteL1 (fun z : {z : ℤ // z ∈ Z} => μ z.val)
        (fun z => ν z.val) := by
  classical
  unfold arithmeticL1 finiteL1
  rw [tsum_eq_sum (s := Z) (fun z hz => by simp [hμ z hz, hν z hz])]
  rw [← Finset.sum_attach Z (fun z : ℤ => |μ z - ν z|)]
  rw [Finset.sum_coe_sort_eq_attach]

private lemma finsetSubtype_sum {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (f : α → β) :
    (∑ x : {x // x ∈ s}, f x.val) = ∑ x ∈ s, f x := by
  classical
  rw [Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach s f

private lemma real_finset_prod_le_two_pow_card {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hnonneg : ∀ i ∈ s, 0 ≤ f i) (hbound : ∀ i ∈ s, f i ≤ 2) :
    ∏ i ∈ s, f i ≤ (2 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hnonnegS : ∀ i ∈ s, 0 ≤ f i := fun i hi => hnonneg i (Finset.mem_insert_of_mem hi)
      have hboundS : ∀ i ∈ s, f i ≤ 2 := fun i hi => hbound i (Finset.mem_insert_of_mem hi)
      have hprodNonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hnonnegS
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      calc
        f a * ∏ i ∈ s, f i ≤ 2 * ∏ i ∈ s, f i :=
          mul_le_mul_of_nonneg_right (hbound a (Finset.mem_insert_self _ _)) hprodNonneg
        _ ≤ 2 * (2 : ℝ) ^ s.card :=
          mul_le_mul_of_nonneg_left (ih hnonnegS hboundS) (by norm_num)
        _ = (2 : ℝ) ^ (s.card + 1) := by rw [pow_succ]; ring

/-- The block product law, including its joint version for fixed pairwise disjoint blocks.
This is Corollary `cor:product-law` (§3 lines 152–166). -/
theorem cor_product_law {n r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (B : Fin r → OAI.SourceBlocks.Block n)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i).set (B j).set)
    (hX : ∀ N j, 4 * primorial (N + 1) ≤ A.X N j)
    (V : ℕ → ℕ) (hV : ∀ N, 1 ≤ V N)
    (hDom : ∀ d, OAI.MicrocellScale.Dominates
      (fun N => Real.log (A.X N (B d).1 : ℝ))
      (fun N => 2 + primorial (N + 1) +
        (∏ j ∈ (B d).2.val, (A.X N j)^2) + V N)) :
    SuperPolynomialSmall
      (fun N => arithmeticL1
        (parameterJointBlockProductMass A N B (hX N))
      (weightedPivotTupleMass A N B))
      (fun N => (V N : ℝ)) := by
  classical
  have hJointFactor (N : ℕ) (z : Fin r → ℤ) :
      parameterJointBlockProductMass A N B (hX N) z =
        ∏ d, parameterBlockProductMass A N (B d) (hX N) (z d) := by
    calc
      _ = ∏ d, localBlockMass A N (B d) (z d) :=
        parameterJointBlockProductMass_eq_localBlockMass_product A N B (hX N) hdisj z
      _ = _ := by
        apply Finset.prod_congr rfl
        intro d hd
        exact localBlockMass_eq_parameterBlockProductMass A N (B d) (hX N) (z d)
  have hBlockSmall (d : Fin r) :
      SuperPolynomialSmall
        (fun N => arithmeticL1 (parameterBlockProductMass A N (B d) (hX N))
          (weightedPivotMass A N (B d))) (fun N => (V N : ℝ)) := by
    let W : ℕ → ℕ := fun N => primorial (N + 1)
    let K : ℕ → ℕ := fun N =>
      ∏ j ∈ (B d).2.val, (A.X N j)^2
    let H : ℕ → ℕ := fun _ => 1
    let X : ℕ → ℕ := fun N => A.X N (B d).1
    let S0 : ℕ → ℝ := fun N => 2 + (W N : ℝ) + (K N : ℝ) + (V N : ℝ)
    let S1 : ℕ → ℝ := fun N => S0 N + 1
    have hK : ∀ N, 1 ≤ K N := by
      intro N
      have hprod : 0 < K N := by
        dsimp [K]
        apply Finset.prod_pos
        intro j hj
        have hW : 0 < primorial (N + 1) := primorial_pos _
        have hXj : 0 < A.X N j := by
          have h4 : 0 < 4 * primorial (N + 1) := Nat.mul_pos (by norm_num) hW
          exact lt_of_lt_of_le h4 (hX N j)
        exact Nat.pow_pos hXj
      dsimp [K] at hprod ⊢
      exact Nat.one_le_iff_ne_zero.mpr hprod.ne'
    have hH : ∀ N, 1 ≤ H N := by intro N; simp [H]
    have hS0 : ∀ N, 1 ≤ S0 N := by
      intro N
      dsimp [S0]
      nlinarith [Nat.cast_nonneg (α := ℝ) (W N), Nat.cast_nonneg (α := ℝ) (K N),
        Nat.cast_nonneg (α := ℝ) (V N)]
    have hS1pos : ∀ N, 0 < S1 N := by
      intro N
      dsimp [S1]
      positivity
    have hS1le : ∀ N, S1 N ≤ 2 * S0 N := by
      intro N
      dsimp [S1]
      nlinarith [hS0 N]
    have hDomLog : OAI.MicrocellScale.Dominates
        (fun N => Real.log (X N : ℝ)) S0 := by
      simpa [S0, W, K, X] using hDom d
    have hDomX0 : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ)) S1 :=
      dominates_nat_of_log_dominates_scale hS0 hS1pos hS1le hDomLog
    have hDomX : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ))
        (fun N => 2 + W N + K N + H N + V N) := by
      simpa [S0, S1, W, K, H, add_assoc, add_comm, add_left_comm] using hDomX0
    have hDomLogX : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
        (fun N => 2 + W N + K N + V N) := by
      simpa [S0, W, K] using hDom d
    have hRatio1 : Tendsto (fun N => Real.log (X N : ℝ) / S0 N) atTop atTop := by
      simpa only [Real.rpow_one] using hDomLog 1 (by norm_num)
    have hKX : ∀ᶠ N in atTop, K N ≤ X N := by
      filter_upwards [hRatio1.eventually_gt_atTop 2] with N hlarge
      have hSpos : 0 < S0 N := by linarith [hS0 N]
      have hloglarge : 2 * S0 N < Real.log (X N : ℝ) :=
        (lt_div_iff₀ hSpos).mp hlarge
      have hKle : (K N : ℝ) ≤ S0 N := by
        dsimp [S0]
        nlinarith [Nat.cast_nonneg (α := ℝ) (W N), Nat.cast_nonneg (α := ℝ) (V N)]
      have hlogle := Real.log_le_self (show (0 : ℝ) ≤ X N by positivity)
      have hNat : (K N : ℝ) ≤ X N := by nlinarith
      exact_mod_cast hNat
    have hXlarge : ∀ᶠ N in atTop, 2 ≤ X N :=
      Filter.Eventually.of_forall fun N => by
        have hW : 0 < primorial (N + 1) := primorial_pos _
        have hcut := hX N (B d).1
        exact le_trans (by omega) hcut
    have hden : ∀ᶠ N in atTop, Real.log (X N) > (W N : ℝ) / X N := by
      filter_upwards [hRatio1.eventually_gt_atTop 2] with N hlarge
      have hSpos : 0 < S0 N := by linarith [hS0 N]
      have hloglarge : 2 * S0 N < Real.log (X N : ℝ) :=
        (lt_div_iff₀ hSpos).mp hlarge
      have hXnat : 0 < X N := by
        dsimp [X]
        have hcut := hX N (B d).1
        exact lt_of_lt_of_le (Nat.mul_pos (by norm_num) (primorial_pos _)) hcut
      have hXpos : 0 < (X N : ℝ) := by exact_mod_cast hXnat
      have hcut : 4 * (W N : ℝ) ≤ X N := by
        dsimp [W, X]
        exact_mod_cast hX N (B d).1
      have hWratio : (W N : ℝ) / X N ≤ 1 / 4 := by
        apply (div_le_iff₀ hXpos).2
        nlinarith [hcut]
      have hlogpos : 2 < Real.log (X N : ℝ) := by nlinarith [hS0 N, hloglarge]
      linarith
    have hAsym := sampling_asymptotics W K H V X
      hK hH hV (by intro N; rfl) hXlarge hden hDomX hDomLogX
    rcases hAsym with ⟨_, _, hDilSmall, _⟩
    have hErrBound : ∀ᶠ N in atTop,
        arithmeticL1 (parameterBlockProductMass A N (B d) (hX N))
          (weightedPivotMass A N (B d)) ≤
          harmonicDilationUniformError (X N) (W N) (K N) := by
      let i := (B d).1
      let T := (B d).2.val
      let R : ℕ → Finset (PivotRest i → ℕ) := fun N =>
        Fintype.piFinset (fun j : PivotRest i =>
          OAI.RawHarmonicProbability.units (A.X N j.val) (W N))
      have hTailPos (N : ℕ) : ∀ r ∈ R N, 1 ≤ blockTailProductOnRest (B d) r := by
        intro r hr
        unfold blockTailProductOnRest
        rw [Finset.prod_coe_sort_eq_attach]
        apply Finset.one_le_prod
        intro j hj
        let q : PivotRest i := ⟨j.val, ne_of_lt ((B d).2.property.2 j.val j.property)⟩
        have hu := Fintype.mem_piFinset.mp hr q
        rcases Finset.mem_filter.mp hu with ⟨hI, _⟩
        have hlo := (Finset.mem_Ico.mp hI).1
        have hWpos : 0 < W N := by dsimp [W]; exact primorial_pos _
        have hcut : 4 * primorial (N + 1) ≤ A.X N j.val := hX N j.val
        have hWone : 1 ≤ primorial (N + 1) :=
          Nat.one_le_iff_ne_zero.mpr (primorial_pos _).ne'
        have hXlo : 1 ≤ A.X N j.val := by nlinarith
        have hXr : A.X N j.val ≤ r q := by simpa [q] using hlo
        exact le_trans hXlo hXr
      have hTailLe (N : ℕ) : ∀ r ∈ R N, blockTailProductOnRest (B d) r ≤ K N := by
        intro r hr
        unfold blockTailProductOnRest
        rw [Finset.prod_coe_sort_eq_attach]
        calc
          _ ≤ ∏ j ∈ (B d).2.val.attach, (A.X N j.val)^2 := by
            apply Finset.prod_le_prod
            · intro j hj
              let q : PivotRest i := ⟨j.val, ne_of_lt ((B d).2.property.2 j.val j.property)⟩
              have hu := Fintype.mem_piFinset.mp hr q
              rcases Finset.mem_filter.mp hu with ⟨hI, _⟩
              exact Nat.le_of_lt (Finset.mem_Ico.mp hI).2
          _ = K N := by
            change (∏ j ∈ T.attach, (A.X N j.val)^2) =
              ∏ j ∈ T, (A.X N j)^2
            exact Finset.prod_attach T (fun j => (A.X N j)^2)
      have hTailCoprime (N : ℕ) : ∀ r ∈ R N,
          Nat.Coprime (blockTailProductOnRest (B d) r) (W N) := by
        intro r hr
        unfold blockTailProductOnRest
        rw [Finset.prod_coe_sort_eq_attach]
        apply Nat.coprime_prod_left_iff.mpr
        intro j hj
        let q : PivotRest i := ⟨j.val, ne_of_lt ((B d).2.property.2 j.val j.property)⟩
        have hu := Fintype.mem_piFinset.mp hr q
        exact (Finset.mem_filter.mp hu).2.symm
      filter_upwards [hKX, hden] with N hKXN hlog
      have hXi : 2 ≤ X N := by
        dsimp [X]
        have hW : 1 ≤ primorial (N + 1) :=
          Nat.one_le_iff_ne_zero.mpr (primorial_pos _).ne'
        have hcut := hX N (B d).1
        omega
      have hPoint : SamplingPointwiseBounds (X N) (W N) :=
        sampling_pointwise_claim (X N) (W N) (primorial_pos _) hXi hlog
      exact parameterBlock_l1_le_dilationError A N (B d) (hX N) hPoint hXi hlog
        (K N) (hK N) hKXN (hTailPos N) (hTailLe N) (hTailCoprime N)
    intro C hC
    have hDil := hDilSmall C hC
    apply squeeze_zero' ?_ ?_ hDil
    · filter_upwards [] with N
      apply mul_nonneg
      · unfold arithmeticL1
        exact tsum_nonneg fun z => abs_nonneg _
      · exact Real.rpow_nonneg (by positivity) C
    filter_upwards [hErrBound] with N hN
    exact mul_le_mul_of_nonneg_right hN (by positivity)
  intro C hC
  let err : Fin r → ℕ → ℝ := fun d N =>
    arithmeticL1 (parameterBlockProductMass A N (B d) (hX N))
      (weightedPivotMass A N (B d))
  have herrNonneg (d : Fin r) (N : ℕ) : 0 ≤ err d N := by
    unfold err arithmeticL1
    exact tsum_nonneg fun z => abs_nonneg _
  have hsmallD (d : Fin r) : ∀ᶠ N in atTop, err d N ≤ 1 := by
    have hlt : ∀ᶠ N in atTop, err d N * (V N : ℝ) < 1 := by
      have := hBlockSmall d 1 (by norm_num)
      filter_upwards [this.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
        with N hN
      simpa [err, Real.rpow_one] using hN
    filter_upwards [hlt] with N hN
    have hVreal : 1 ≤ (V N : ℝ) := by exact_mod_cast hV N
    have hmul : err d N ≤ err d N * (V N : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hVreal (herrNonneg d N)
    linarith
  have hsmallAll : ∀ᶠ N in atTop, ∀ d, err d N ≤ 1 := by
    rw [Filter.eventually_all]
    exact fun d => hsmallD d
  have hProductBound (N : ℕ) (hsmall : ∀ d, err d N ≤ 1) :
      arithmeticL1 (parameterJointBlockProductMass A N B (hX N))
          (weightedPivotTupleMass A N B) ≤
        (2 : ℝ) ^ r * ∑ d, err d N := by
    let Z : Finset ℤ := Finset.Icc (0 : ℤ)
      (parameterGlobalProductCutoff A N : ℤ)
    let α := {z : ℤ // z ∈ Z}
    let μfull : Fin r → ℤ → ℝ := fun d z =>
      parameterBlockProductMass A N (B d) (hX N) z
    let νfull : Fin r → ℤ → ℝ := fun d z => weightedPivotMass A N (B d) z
    let μ : Fin r → α → ℝ := fun d z => μfull d z.val
    let ν : Fin r → α → ℝ := fun d z => νfull d z.val
    have hμsupport (d : Fin r) (z : ℤ) (hz : z ∉ Z) : μfull d z = 0 := by
      exact parameterBlockProductMass_zero_outside_globalCutoff A N (B d)
        (hX N) z (by simpa [Z] using hz)
    have hνsupport (d : Fin r) (z : ℤ) (hz : z ∉ Z) : νfull d z = 0 := by
      exact weightedPivotMass_zero_outside_globalCutoff A N (B d) (hX N) z
        (by simpa [Z] using hz)
    have hJointId :
        arithmeticL1 (parameterJointBlockProductMass A N B (hX N))
            (weightedPivotTupleMass A N B) =
          finiteL1 (fun x : Fin r → α => ∏ d, μ d (x d))
            (fun x => ∏ d, ν d (x d)) := by
      calc
        _ = arithmeticL1 (fun z : Fin r → ℤ => ∏ d, μfull d (z d))
              (fun z => ∏ d, νfull d (z d)) := by
                unfold arithmeticL1
                apply tsum_congr
                intro z
                rw [hJointFactor N z]
                rfl
        _ = _ := arithmeticL1_pi_product_eq_finiteL1 Z μfull νfull
          (fun d z hz => hμsupport d z hz) (fun d z hz => hνsupport d z hz)
    have hμnonneg (d : Fin r) (z : ℤ) : 0 ≤ μfull d z := by
      dsimp [μfull]
      unfold parameterBlockProductMass
      split_ifs with hz
      · exact measureReal_nonneg
      · exact le_of_eq rfl
    have hμnorm (d : Fin r) : (∑ z : α, |μ d z|) = 1 := by
      calc
        _ = ∑ z ∈ Z, |μfull d z| := finsetSubtype_sum Z (fun z => |μfull d z|)
        _ = ∑ z ∈ Z, μfull d z := by
          apply Finset.sum_congr rfl
          intro z hz
          exact abs_of_nonneg (hμnonneg d z)
        _ = 1 := by
          simpa [Z, μfull] using
            parameterBlockProductMass_sum_globalCutoff A N (B d) (hX N)
    have hlocalEq (d : Fin r) :
        arithmeticL1 (μfull d) (νfull d) = finiteL1 (μ d) (ν d) := by
      exact arithmeticL1_eq_finiteL1_of_support Z (μfull d) (νfull d)
        (fun z hz => hμsupport d z hz) (fun z hz => hνsupport d z hz)
    have hνnorm (d : Fin r) : (∑ z : α, |ν d z|) ≤ 2 := by
      have htriangle :
          (∑ z : α, |ν d z|) ≤
            (∑ z : α, |μ d z|) + finiteL1 (μ d) (ν d) := by
        calc
          _ ≤ ∑ z : α, (|μ d z| + |μ d z - ν d z|) := by
            apply Finset.sum_le_sum
            intro z hz
            calc
              |ν d z| = |μ d z - (μ d z - ν d z)| := by congr 1 <;> ring
              _ ≤ |μ d z| + |μ d z - ν d z| := abs_sub _ _
          _ = _ := by
            simp only [finiteL1]
            rw [Finset.sum_add_distrib]
      calc
        _ ≤ (∑ z : α, |μ d z|) + finiteL1 (μ d) (ν d) := htriangle
        _ = 1 + err d N := by rw [hμnorm d, ← hlocalEq d]
        _ ≤ 2 := by linarith [hsmall d]
    have hfactor (d : Fin r) :
        ∏ j ∈ Finset.univ.erase d,
            max (∑ z : α, |μ j z|) (∑ z : α, |ν j z|) ≤ (2 : ℝ) ^ r := by
      have hbase := real_finset_prod_le_two_pow_card
        (Finset.univ.erase d)
        (fun j => max (∑ z : α, |μ j z|) (∑ z : α, |ν j z|))
        (fun j hj => le_max_of_le_left (Finset.sum_nonneg fun z hz => abs_nonneg _))
        (fun j hj => max_le (by rw [hμnorm j]; norm_num) (hνnorm j))
      have hcard : (Finset.univ.erase d).card ≤ r := by
        have hc := Finset.card_le_card (Finset.erase_subset d (Finset.univ : Finset (Fin r)))
        simpa using hc
      exact hbase.trans (pow_le_pow_right₀ (by norm_num) hcard)
    have htel := finite_product_l1_telescoping
      (ι := Fin r) (α := α) (μ := μ) (ν := ν)
    have hfiniteBound :
        finiteL1 (fun x : Fin r → α => ∏ d, μ d (x d))
          (fun x => ∏ d, ν d (x d)) ≤
          (2 : ℝ) ^ r * ∑ d, err d N := by
      calc
        _ ≤ ∑ d, finiteL1 (μ d) (ν d) *
            ∏ j ∈ Finset.univ.erase d,
              max (∑ z : α, |μ j z|) (∑ z : α, |ν j z|) := htel
        _ ≤ ∑ d, err d N * (2 : ℝ) ^ r := by
          apply Finset.sum_le_sum
          intro d hd
          have hloc : finiteL1 (μ d) (ν d) = err d N := by
              simpa [err] using (hlocalEq d).symm
          have hfactornonneg : 0 ≤
              ∏ j ∈ Finset.univ.erase d,
                max (∑ z : α, |μ j z|) (∑ z : α, |ν j z|) := by positivity
          calc
            _ ≤ err d N *
                ∏ j ∈ Finset.univ.erase d,
                  max (∑ z : α, |μ j z|) (∑ z : α, |ν j z|) := by
                    rw [hloc]
            _ ≤ err d N * (2 : ℝ) ^ r :=
              mul_le_mul_of_nonneg_left (hfactor d) (herrNonneg d N)
        _ = (∑ d, err d N) * (2 : ℝ) ^ r := by rw [Finset.sum_mul]
        _ = (2 : ℝ) ^ r * ∑ d, err d N := by ring
    rw [hJointId]
    exact hfiniteBound
  have hsum :
      Tendsto (fun N => ∑ d, err d N * (V N : ℝ) ^ C) atTop (𝓝 0) := by
    have hterm (d : Fin r) :
        Tendsto (fun N => err d N * (V N : ℝ) ^ C) atTop (𝓝 0) := by
      simpa [err] using hBlockSmall d C hC
    have hind : ∀ s : Finset (Fin r),
        Tendsto (fun N => ∑ d ∈ s, err d N * (V N : ℝ) ^ C) atTop (𝓝 0) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          have heq : (fun N => ∑ d ∈ insert a s, err d N * (V N : ℝ) ^ C) =
              fun N => err a N * (V N : ℝ) ^ C +
                ∑ d ∈ s, err d N * (V N : ℝ) ^ C := by
            funext N
            rw [Finset.sum_insert ha]
          rw [heq]
          simpa using (hterm a).add ih
    simpa using hind Finset.univ
  have hUpper : ∀ᶠ N in atTop,
      arithmeticL1 (parameterJointBlockProductMass A N B (hX N))
          (weightedPivotTupleMass A N B) * (V N : ℝ) ^ C ≤
        (2 : ℝ) ^ r * ∑ d, err d N * (V N : ℝ) ^ C := by
    filter_upwards [hsmallAll] with N hsmall
    have hB := hProductBound N hsmall
    have hpow : 0 ≤ (V N : ℝ) ^ C := Real.rpow_nonneg (by positivity) C
    calc
      _ ≤ ((2 : ℝ) ^ r * ∑ d, err d N) * (V N : ℝ) ^ C :=
        mul_le_mul_of_nonneg_right hB hpow
      _ = (2 : ℝ) ^ r * ((∑ d, err d N) * (V N : ℝ) ^ C) := by ring
      _ = (2 : ℝ) ^ r * ∑ d, err d N * (V N : ℝ) ^ C := by
        rw [Finset.sum_mul]
  have hUpperTendsto :
      Tendsto (fun N => (2 : ℝ) ^ r * ∑ d, err d N * (V N : ℝ) ^ C)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ) ^ r) atTop (𝓝 ((2 : ℝ) ^ r))).mul hsum
  apply squeeze_zero' (Filter.Eventually.of_forall fun N => by
    unfold arithmeticL1
    apply mul_nonneg
    · exact tsum_nonneg fun z => abs_nonneg _
    · exact Real.rpow_nonneg (by positivity) C) hUpper hUpperTendsto

/-- Conditioning on `t_T=σ` expresses the block-product law as the mixture of the pivot
dilation laws (§3 lines 168–172). -/
theorem block_product_mass_conditioning_formula {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n)
    (hX : ∀ j, 4 * primorial (N + 1) ≤ A.X N j) :
    ∀ z : ℤ, parameterBlockProductMass A N B hX z =
      ∑' σ : ℕ, parameterTailProductLaw A N B.2.val σ *
        dilatedLaw (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ z := by
  classical
  intro z
  by_cases hz : 0 ≤ z
  · let W := primorial (N + 1)
    let i := B.1
    let T := B.2.val
    let U : Fin n → Finset ℕ := fun j =>
      OAI.RawHarmonicProbability.units (A.X N j) W
    let R : Finset (PivotRest i → ℕ) :=
      Fintype.piFinset (fun j : PivotRest i => U j.val)
    let restWeight (r : PivotRest i → ℕ) : ℝ :=
      ∏ j : PivotRest i, harmonicNatLaw (A.X N j.val) W (r j)
    have hnoti : i ∉ T := by
      intro hmem
      exact (lt_irrefl i) (B.2.property.2 i hmem)
    have htail (σ : ℕ) : parameterTailProductLaw A N T σ =
        ∑ r ∈ R, if blockTailProductOnRest B r = σ then restWeight r else 0 := by
      simpa [R, U, W, restWeight, blockTailProductOnRest, Finset.prod_coe_sort] using
        parameterTailProductLaw_pivot_independent A N T i hnoti (hX) σ
    let S : Finset ℕ := R.image (blockTailProductOnRest B)
    have htail_zero {σ : ℕ} (hσ : σ ∉ S) : parameterTailProductLaw A N T σ = 0 := by
      rw [htail σ]
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hprod : blockTailProductOnRest B r = σ
      · exact (hσ (Finset.mem_image.mpr ⟨r, hr, hprod⟩)).elim
      · simp [hprod]
    have hmix :
        (∑' σ : ℕ, parameterTailProductLaw A N T σ *
          dilatedLaw (harmonicLaw (A.X N i) W) σ z) =
        ∑ r ∈ R, restWeight r *
          dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z := by
      rw [tsum_eq_sum (s := S)]
      · calc
          _ = ∑ σ ∈ S,
                (∑ r ∈ R, if blockTailProductOnRest B r = σ then restWeight r else 0) *
                  dilatedLaw (harmonicLaw (A.X N i) W) σ z := by
                    apply Finset.sum_congr rfl
                    intro σ hσ
                    rw [htail σ]
          _ = ∑ σ ∈ S, ∑ r ∈ R,
                (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                  dilatedLaw (harmonicLaw (A.X N i) W) σ z := by
                    simp_rw [Finset.sum_mul]
          _ = ∑ r ∈ R, ∑ σ ∈ S,
                (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                  dilatedLaw (harmonicLaw (A.X N i) W) σ z := by
                    rw [Finset.sum_comm]
          _ = ∑ r ∈ R, restWeight r *
                dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hmem : blockTailProductOnRest B r ∈ S :=
                    Finset.mem_image.mpr ⟨r, hr, rfl⟩
                  rw [show (∑ σ ∈ S,
                    (if blockTailProductOnRest B r = σ then restWeight r else 0) *
                      dilatedLaw (harmonicLaw (A.X N i) W) σ z) =
                    ∑ σ ∈ S, if blockTailProductOnRest B r = σ then
                      restWeight r * dilatedLaw (harmonicLaw (A.X N i) W) σ z else 0 by
                        apply Finset.sum_congr rfl
                        intro σ hσ
                        by_cases heq : blockTailProductOnRest B r = σ <;> simp [heq]]
                  rw [Finset.sum_ite_eq]
                  simp [hmem]
      · intro σ hσ
        simp [htail_zero hσ]
    have hmass := parameterBlockProductMass_pivot_split A N B (hX) z hz
    have hmass' : parameterBlockProductMass A N B (hX) z =
        ∑ r ∈ R,
          (∑ a ∈ U i,
            if blockTailProductOnRest B r * a = z.toNat then
              harmonicNatLaw (A.X N i) W a else 0) * restWeight r := by
      rw [hmass]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases heq : blockTailProductOnRest B r * a = z.toNat
      · simp [heq, i, W, restWeight]
      · have heq' : a * blockTailProductOnRest B r ≠ z.toNat := by
          simpa [Nat.mul_comm] using heq
        simp [heq, heq', i, W, restWeight]
    have hpositive (r : PivotRest i → ℕ) (hr : r ∈ R) :
        0 < blockTailProductOnRest B r := by
      unfold blockTailProductOnRest
      apply Finset.prod_pos
      intro j hj
      have hj' : r ⟨j.val, ne_of_lt (B.2.property.2 j.val j.property)⟩ ∈ U j.val :=
        (Fintype.mem_piFinset.mp hr) ⟨j.val, ne_of_lt (B.2.property.2 j.val j.property)⟩
      have hWpos : 0 < W := by dsimp [W]; exact primorial_pos _
      have hXj : 4 * W ≤ A.X N j.val := by simpa [W] using hX j.val
      have hXpos : 0 < A.X N j.val := by
        have h4W : 0 < 4 * W := by omega
        exact lt_of_lt_of_le h4W hXj
      have hge : A.X N j.val ≤ r ⟨j.val, ne_of_lt (B.2.property.2 j.val j.property)⟩ :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hj').1).1
      omega
    have hinner (r : PivotRest i → ℕ) (hr : r ∈ R) :
        (∑ a ∈ U i,
          if blockTailProductOnRest B r * a = z.toNat then
            harmonicNatLaw (A.X N i) W a else 0) =
          dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z := by
      exact (dilatedLaw_eq_pivot_sum (A.X N i) W (blockTailProductOnRest B r) z
        (hpositive r hr) hz).symm
    calc
      parameterBlockProductMass A N B (hX) z =
          ∑ r ∈ R, restWeight r *
            dilatedLaw (harmonicLaw (A.X N i) W) (blockTailProductOnRest B r) z := by
              rw [hmass']
              apply Finset.sum_congr rfl
              intro r hr
              rw [hinner r hr]
              ring
      _ = ∑' σ : ℕ, parameterTailProductLaw A N T σ *
            dilatedLaw (harmonicLaw (A.X N i) W) σ z := hmix.symm
  · have hzneg : z < 0 := lt_of_not_ge hz
    have hmass0 : parameterBlockProductMass A N B (hX) z = 0 := by
      rw [parameterBlockProductMass_finset]
      simp [hz]
    rw [hmass0]
    have hdil (σ : ℕ) :
        dilatedLaw (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ z = 0 := by
      exact dilatedLaw_zero_of_negative (A.X N B.1) (primorial (N + 1)) σ hzneg
    rw [tsum_eq_single 0]
    · simp [hdil]
    · intro σ hσ
      simp [hdil]

/-- Averaging the unnormalized dilation reference measures gives the divisor-weighted pivot
law `ν_B μ_i` exactly (§3 lines 172–182). -/
theorem block_product_weight_average_is_nu {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : OAI.SourceBlocks.Block n) (z : ℤ) :
    (∑' σ : ℕ, parameterTailProductLaw A N B.2.val σ *
      dilationReference (harmonicLaw (A.X N B.1) (primorial (N + 1))) σ z) =
      weightedPivotMass A N B z := by
  classical
  unfold weightedPivotMass nuB dilationReference
  rw [← tsum_mul_right]
  apply tsum_congr
  intro σ
  by_cases hdiv : (σ : ℤ) ∣ z <;> simp [hdiv] <;> ring

end
end HindmanSumsProducts
