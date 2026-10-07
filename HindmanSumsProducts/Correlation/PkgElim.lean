import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the §4 proof package `Elim` (owned by its proof lane). -/

namespace HindmanSumsProducts
open Filter
open FromArithmetic
open scoped Topology

/-- Encode a chain tail as the finite-coordinate divisor template used by §3. -/
noncomputable def tailDivisorTemplate {n : ℕ} (T : Finset (Fin n)) :
    DivisorTemplate n n where
  arity := T.card
  arity_le := by simpa using Finset.card_le_univ T
  cutoff i := ((T.equivFinOfCardEq rfl).symm i).val

/-- An arity-zero divisor template contributes the constant weight one. -/
theorem nuB_divisorTemplate_arity_zero {n b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (D : DivisorTemplate n b) (hD : D.arity = 0) (y : ℤ) :
    nuB (divisorTemplateLaw A N D) y = 1 := by
  cases D with
  | mk arity arity_le cutoff =>
    have hzero : arity = 0 := hD
    subst arity
    simp [nuB, divisorTemplateLaw, harmonicProductLaw]
    rw [tsum_eq_single 1]
    · simp
    · intro σ hσ
      have hn : 1 ≠ σ := fun heq => hσ heq.symm
      simp [hn]

theorem harmonicNormalizer_eq_rawMass (X W : ℕ) :
    harmonicNormalizer X W = OAI.DyadicHarmonicBoundary.mass X (X ^ 2) W := by
  rw [OAI.RawHarmonicProbability.mass_units]
  simp [harmonicNormalizer, OAI.RawHarmonicProbability.units,
    Nat.coprime_comm, div_eq_mul_inv]

theorem harmonicNatLaw_tsum_one {X W : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  classical
  have hZpos : 0 < harmonicNormalizer X W := by
    rw [harmonicNormalizer_eq_rawMass]
    exact OAI.RawHarmonicProbability.mass_pos X W hW hX
  have hZ : harmonicNormalizer X W ≠ 0 := ne_of_gt hZpos
  have hsupp : ∀ n ∉ Finset.Ico X (X ^ 2), harmonicNatLaw X W n = 0 := by
    intro n hn
    unfold harmonicNatLaw
    rw [if_neg]
    intro hh
    exact hn (Finset.mem_Ico.mpr ⟨hh.1, hh.2.1⟩)
  rw [tsum_eq_sum hsupp]
  have hsum :
      (∑ n ∈ Finset.Ico X (X ^ 2), harmonicNatLaw X W n) =
        (∑ n ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime n W then 1 / (n : ℝ) else 0) /
          harmonicNormalizer X W := by
    calc
      _ = ∑ n ∈ Finset.Ico X (X ^ 2),
          (if Nat.Coprime n W then 1 / (n : ℝ) else 0) *
            (harmonicNormalizer X W)⁻¹ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hmem := Finset.mem_Ico.mp hn
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hmem.1))
          by_cases hc : Nat.Coprime n W
          · simp [harmonicNatLaw, hmem, hc, hn0, div_eq_mul_inv]
            ring_nf
          · simp [harmonicNatLaw, hmem, hc, div_eq_mul_inv]
      _ = (∑ n ∈ Finset.Ico X (X ^ 2),
          if Nat.Coprime n W then 1 / (n : ℝ) else 0) *
            (harmonicNormalizer X W)⁻¹ := by rw [Finset.sum_mul]
      _ = _ := by rw [div_eq_mul_inv]
  have hmassEq :
      (∑ n ∈ Finset.Ico X (X ^ 2), if Nat.Coprime n W then 1 / (n : ℝ) else 0) =
        harmonicNormalizer X W := by
    unfold harmonicNormalizer
    rw [← Finset.sum_filter]
  have hmass :
      (∑ n ∈ Finset.Ico X (X ^ 2), if Nat.Coprime n W then 1 / (n : ℝ) else 0) ≠ 0 := by
    rw [hmassEq]
    exact hZ
  rw [hsum, ← hmassEq]
  field_simp [hmass]

theorem harmonicNatLaw_sum_units {X W : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X) :
    ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
      harmonicNatLaw X W n = 1 := by
  classical
  have hnat :
      ∑ n ∈ Finset.Ico X (X ^ 2), harmonicNatLaw X W n = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := harmonicNatLaw X W) (s := Finset.Ico X (X ^ 2))]
    · exact harmonicNatLaw_tsum_one hW hX
    · intro n hn
      unfold harmonicNatLaw
      rw [if_neg]
      intro h
      exact hn (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)
  calc
    _ = ∑ n ∈ Finset.Ico X (X ^ 2),
        if Nat.Coprime n W then harmonicNatLaw X W n else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Ico X (X ^ 2), harmonicNatLaw X W n := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hc : Nat.Coprime n W <;> simp [harmonicNatLaw, hn, hc]
    _ = 1 := hnat

theorem pkgElim_harmonicLaw_tsum_one {X W : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X) :
    ∑' z : ℤ, harmonicLaw X W z = 1 := by
  classical
  let s : Finset ℤ := (Finset.Ico X (X ^ 2)).image fun n : ℕ => (n : ℤ)
  have hsupp : ∀ z ∉ s, harmonicLaw X W z = 0 := by
    intro z hz
    unfold harmonicLaw
    rw [if_neg]
    intro h
    apply hz
    change z ∈ (Finset.Ico X (X ^ 2)).image fun n : ℕ => (n : ℤ)
    refine Finset.mem_image.mpr ⟨z.toNat, Finset.mem_Ico.mpr ?_, ?_⟩
    · exact ⟨by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1⟩
    · exact Int.toNat_of_nonneg h.1
  rw [tsum_eq_sum hsupp]
  have himg : ∑ z ∈ s, harmonicLaw X W z =
      ∑ n ∈ Finset.Ico X (X ^ 2), harmonicNatLaw X W n := by
    dsimp only [s]
    rw [Finset.sum_image (s := Finset.Ico X (X ^ 2))
      (g := fun n : ℕ => (n : ℤ)) (f := harmonicLaw X W)
      (by
        intro n hn m hm hnm
        exact Int.ofNat.inj hnm)]
    apply Finset.sum_congr rfl
    intro n hn
    simp [harmonicLaw, harmonicNatLaw]
  rw [himg, ← tsum_eq_sum (L := SummationFilter.unconditional ℕ)
    (f := harmonicNatLaw X W)
    (s := Finset.Ico X (X ^ 2)) (by
    intro n hn
    unfold harmonicNatLaw
    rw [if_neg]
    intro h
    exact hn (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))]
  exact harmonicNatLaw_tsum_one hW hX

theorem harmonicLaw_sum_support {X W : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X) :
    ∑ z ∈ (Finset.Ico X (X ^ 2)).image (fun n : ℕ => (n : ℤ)),
      harmonicLaw X W z = 1 := by
  classical
  let s : Finset ℤ := (Finset.Ico X (X ^ 2)).image (fun n : ℕ => (n : ℤ))
  have hsupp : ∀ z ∉ s, harmonicLaw X W z = 0 := by
    intro z hz
    unfold harmonicLaw
    rw [if_neg]
    intro h
    apply hz
    refine Finset.mem_image.mpr ⟨z.toNat, Finset.mem_Ico.mpr ?_, ?_⟩
    · exact ⟨by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1⟩
    · exact Int.toNat_of_nonneg h.1
  change (∑ z ∈ s, harmonicLaw X W z) = 1
  rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (f := harmonicLaw X W) (s := s) hsupp]
  exact pkgElim_harmonicLaw_tsum_one hW hX

theorem harmonicNatProduct_tsum_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ℕ} (X : ι → ℕ) (hW : 0 < W) (hX : ∀ i, 4 * W ≤ X i) :
    ∑' t : ι → ℕ, ∏ i, harmonicNatLaw (X i) W (t i) = 1 := by
  classical
  let I : ι → Finset ℕ := fun i =>
    (Finset.Ico (X i) ((X i) ^ 2)).filter fun k => Nat.Coprime k W
  let s : Finset (ι → ℕ) :=
    Fintype.piFinset I
  have hcoord (i : ι) :
      ∑ k ∈ I i, harmonicNatLaw (X i) W k = 1 := by
    have hnat : ∑ k ∈ Finset.Ico (X i) ((X i) ^ 2),
        harmonicNatLaw (X i) W k = 1 := by
      rw [← tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (f := harmonicNatLaw (X i) W) (s := Finset.Ico (X i) ((X i) ^ 2))]
      · exact harmonicNatLaw_tsum_one hW (hX i)
      · intro k hk
        unfold harmonicNatLaw
        rw [if_neg]
        intro h
        exact hk (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)
    calc
      ∑ k ∈ I i, harmonicNatLaw (X i) W k =
          ∑ k ∈ Finset.Ico (X i) ((X i) ^ 2),
            if Nat.Coprime k W then harmonicNatLaw (X i) W k else 0 := by
        dsimp [I]
        rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Ico (X i) ((X i) ^ 2), harmonicNatLaw (X i) W k := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hc : Nat.Coprime k W <;> simp [harmonicNatLaw, hk, hc]
      _ = 1 := hnat
  have hsupp : ∀ t ∉ s, (∏ i, harmonicNatLaw (X i) W (t i)) = 0 := by
    intro t ht
    have hnotall : ∃ i, t i ∉ I i := by
      by_contra h
      push_neg at h
      have hv : t ∈ Fintype.piFinset I := by simpa using h
      apply ht
      simpa [s] using hv
    obtain ⟨i, hi⟩ := hnotall
    have hcond : ¬ (X i ≤ t i ∧ t i < (X i) ^ 2 ∧ Nat.Coprime (t i) W) := by
      intro h
      exact hi (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [harmonicNatLaw, hcond]
  rw [tsum_eq_sum hsupp]
  rw [← Finset.prod_univ_sum]
  calc
    ∏ i, ∑ k ∈ I i, harmonicNatLaw (X i) W k = ∏ _i : ι, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hcoord i
    _ = 1 := by simp

theorem productLaw_tsum_one_of_finite_support {ι α : Type*} [Fintype ι]
    [DecidableEq ι]
    (μ : ι → α → ℝ) (S : ι → Finset α)
    (hsupp : ∀ i z, z ∉ S i → μ i z = 0)
    (hnorm : ∀ i, ∑ z ∈ S i, μ i z = 1) :
    ∑' x : ι → α, ∏ i, μ i (x i) = 1 := by
  classical
  let β : ι → Type _ := fun i => {z : α // z ∈ S i}
  letI : ∀ i, Fintype (β i) := fun i => Finset.Subtype.fintype (S i)
  let rawMap (x : ∀ i, β i) : ι → α := fun i => (x i).val
  let support : Finset (ι → α) := Finset.univ.image rawMap
  have hinj : Function.Injective rawMap := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  have hzero : ∀ x ∉ support, (∏ i, μ i (x i)) = 0 := by
    intro x hx
    have hnotall : ∃ i, x i ∉ S i := by
      by_contra h
      push_neg at h
      apply hx
      refine Finset.mem_image.mpr
        ⟨(fun i => (⟨x i, h i⟩ : β i)), Finset.mem_univ _, ?_⟩
      funext i
      rfl
    obtain ⟨i, hi⟩ := hnotall
    have hμ : μ i (x i) = 0 := hsupp i (x i) hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) hμ
  rw [tsum_eq_sum hzero]
  rw [Finset.sum_image (s := Finset.univ) (g := rawMap)
    (f := fun x : ι → α => ∏ i, μ i (x i)) hinj.injOn]
  let box : ∀ i : ι, Finset (β i) := fun _ => Finset.univ
  have hPi : Fintype.piFinset box = (Finset.univ : Finset (∀ i, β i)) := by
    ext x
    simp [box]
  have hprodSum := Finset.prod_univ_sum box (fun i z => μ i z.val)
  rw [hPi] at hprodSum
  calc
    ∑ x : (∀ i, β i), ∏ i, μ i (x i).val =
        ∏ i, ∑ z : β i, μ i z.val := by
      simpa [box] using hprodSum.symm
    _ = ∏ _i : ι, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      change ∑ z ∈ (S i).attach, μ i z.val = 1
      rw [Finset.sum_attach]
      exact hnorm i
    _ = 1 := by simp

theorem product_tsum_eq_product_sum_of_finite_support {ι α : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → α → ℝ) (S : ι → Finset α)
    (hsupp : ∀ i z, z ∉ S i → f i z = 0) :
    ∑' x : ι → α, ∏ i, f i (x i) = ∏ i, ∑ z ∈ S i, f i z := by
  classical
  let β : ι → Type _ := fun i => {z : α // z ∈ S i}
  letI : ∀ i, Fintype (β i) := fun i => Finset.Subtype.fintype (S i)
  let rawMap (x : ∀ i, β i) : ι → α := fun i => (x i).val
  let support : Finset (ι → α) := Finset.univ.image rawMap
  have hinj : Function.Injective rawMap := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  have hzero : ∀ x ∉ support, (∏ i, f i (x i)) = 0 := by
    intro x hx
    have hnotall : ∃ i, x i ∉ S i := by
      by_contra h
      push_neg at h
      apply hx
      refine Finset.mem_image.mpr
        ⟨(fun i => (⟨x i, h i⟩ : β i)), Finset.mem_univ _, ?_⟩
      funext i
      rfl
    obtain ⟨i, hi⟩ := hnotall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hsupp i (x i) hi)
  rw [tsum_eq_sum hzero]
  rw [Finset.sum_image (s := Finset.univ) (g := rawMap)
    (f := fun x : ι → α => ∏ i, f i (x i)) hinj.injOn]
  let box : ∀ i : ι, Finset (β i) := fun _ => Finset.univ
  have hPi : Fintype.piFinset box = (Finset.univ : Finset (∀ i, β i)) := by
    ext x
    simp [box]
  have hprodSum := Finset.prod_univ_sum box (fun i z => f i z.val)
  rw [hPi] at hprodSum
  calc
    ∑ x : (∀ i, β i), ∏ i, f i (x i).val =
        ∏ i, ∑ z : β i, f i z.val := by
      simpa [box] using hprodSum.symm
    _ = ∏ i, ∑ z ∈ S i, f i z := by
      apply Finset.prod_congr rfl
      intro i hi
      change ∑ z ∈ (S i).attach, f i z.val = _
      rw [Finset.sum_attach]

theorem function_eq_indicator_prod {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f g : ι → α) :
    (if f = g then 1 else 0 : ℝ) = ∏ i, (if f i = g i then 1 else 0 : ℝ) := by
  classical
  by_cases h : f = g
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro i hi
    simp [congrFun h i]
  · have hnot : ∃ i, f i ≠ g i := by
      by_contra hall
      push_neg at hall
      apply h
      funext i
      exact hall i
    obtain ⟨i, hi⟩ := hnot
    have hzero : (if f i = g i then 1 else 0 : ℝ) = 0 := by simp [hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
    simp [h]

theorem productBaseResidueLaw_eq_product {d K : ℕ} (hK : 0 < K)
    (μ : Fin d → ℤ → ℝ) (S : Fin d → Finset ℤ)
    (hsupp : ∀ i z, z ∉ S i → μ i z = 0) (r : Fin d → Fin K) :
    FromArithmetic.baseResidueLaw K hK (fun x => ∏ i, μ i (x i)) r =
      ∏ i, ∑' z : ℤ,
        μ i z * (if FromArithmetic.integerResidue K hK z = r i then 1 else 0) := by
  classical
  let g : Fin d → ℤ → ℝ := fun i z =>
    μ i z * (if FromArithmetic.integerResidue K hK z = r i then 1 else 0)
  have hterm (x : Fin d → ℤ) :
      (∏ i, μ i (x i)) *
          (if (fun i => FromArithmetic.integerResidue K hK (x i)) = r then 1 else 0) =
        ∏ i, g i (x i) := by
    by_cases heq : (fun i => FromArithmetic.integerResidue K hK (x i)) = r
    · rw [if_pos heq]
      simp only [mul_one]
      apply Finset.prod_congr rfl
      intro i hi
      simp [g, congrFun heq i]
    · have hnotall : ∃ i, FromArithmetic.integerResidue K hK (x i) ≠ r i := by
        by_contra h
        push_neg at h
        apply heq
        funext i
        exact h i
      obtain ⟨i, hi⟩ := hnotall
      have hzero : g i (x i) = 0 := by simp [g, hi]
      have hprod : (∏ j, g j (x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [heq, hprod]
  unfold FromArithmetic.baseResidueLaw
  calc
    (∑' x : Fin d → ℤ,
        (∏ i, μ i (x i)) *
          (if (fun i => FromArithmetic.integerResidue K hK (x i)) = r then 1 else 0)) =
        ∑' x : Fin d → ℤ, ∏ i, g i (x i) := by
      apply tsum_congr
      intro x
      exact hterm x
    _ = ∏ i, ∑ z ∈ S i, g i z :=
      product_tsum_eq_product_sum_of_finite_support g S
        (fun i z hz => by simp [g, hsupp i z hz])
    _ = ∏ i, ∑' z : ℤ, g i z := by
      apply Finset.prod_congr rfl
      intro i hi
      symm
      rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
        (f := g i) (s := S i) (fun z hz => by simp [g, hsupp i z hz])]
    _ = _ := by simp [g]

theorem finiteL1_product_probability_le {ι α : Type*} [Fintype ι] [Fintype α]
    [Fintype (ι → α)] [DecidableEq ι]
    (μ ν : ι → α → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x) (hν : ∀ i x, 0 ≤ ν i x)
    (hμnorm : ∀ i, ∑ x, μ i x = 1) (hνnorm : ∀ i, ∑ x, ν i x = 1) :
    finiteL1 (fun x : ι → α => ∏ i, μ i (x i))
      (fun x : ι → α => ∏ i, ν i (x i)) ≤ ∑ i, finiteL1 (μ i) (ν i) := by
  classical
  have hμabs (i : ι) : ∑ x, |μ i x| = 1 := by
    calc
      _ = ∑ x, μ i x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_of_nonneg (hμ i x)]
      _ = 1 := hμnorm i
  have hνabs (i : ι) : ∑ x, |ν i x| = 1 := by
    calc
      _ = ∑ x, ν i x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_of_nonneg (hν i x)]
      _ = 1 := hνnorm i
  calc
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) *
        ∏ j ∈ Finset.univ.erase i,
          max (∑ x, |μ j x|) (∑ x, |ν j x|) :=
      FromArithmetic.finite_product_l1_telescoping μ ν
    _ = ∑ i, finiteL1 (μ i) (ν i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hμabs, hνabs]

noncomputable def finitePushforward {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (b : β) : ℝ :=
  ∑ a, if f a = b then μ a else 0

theorem finiteL1_pushforward_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (μ ν : α → ℝ) :
    finiteL1 (finitePushforward f μ) (finitePushforward f ν) ≤ finiteL1 μ ν := by
  classical
  have hinner (a : α) :
      ∑ b : β,
        |(if f a = b then μ a else 0) - (if f a = b then ν a else 0)| =
          |μ a - ν a| := by
    have hterm (b : β) :
        |(if f a = b then μ a else 0) - (if f a = b then ν a else 0)| =
          if b = f a then |μ a - ν a| else 0 := by
      by_cases h : b = f a
      · subst b
        simp
      · have h' : f a ≠ b := Ne.symm h
        simp [h, h']
    calc
      _ = ∑ b : β, if b = f a then |μ a - ν a| else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hterm b
      _ = |μ a - ν a| := by simp
  unfold finiteL1 finitePushforward
  calc
    (∑ b : β,
        |(∑ a, if f a = b then μ a else 0) -
          ∑ a, if f a = b then ν a else 0|) ≤
      ∑ b : β, ∑ a, |(if f a = b then μ a else 0) - (if f a = b then ν a else 0)| := by
        apply Finset.sum_le_sum
        intro b hb
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |μ a - ν a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact hinner a

noncomputable def integerResidueLaw (K : ℕ) (hK : 0 < K) (μ : ℤ → ℝ) : Fin K → ℝ :=
  fun a => ∑' z : ℤ,
    μ z * (if FromArithmetic.integerResidue K hK z = a then 1 else 0)

theorem integerResidueLaw_nonneg {K : ℕ} (hK : 0 < K) (μ : ℤ → ℝ)
    (S : Finset ℤ) (hsupp : ∀ z ∉ S, μ z = 0) (hμ : ∀ z, 0 ≤ μ z) (a : Fin K) :
    0 ≤ integerResidueLaw K hK μ a := by
  classical
  unfold integerResidueLaw
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (f := fun z => μ z * (if FromArithmetic.integerResidue K hK z = a then 1 else 0))
    (s := S) (by intro z hz; simp [hsupp z hz])]
  apply Finset.sum_nonneg
  intro z hz
  exact mul_nonneg (hμ z) (by split_ifs <;> positivity)

theorem integerResidueLaw_sum_one {K : ℕ} (hK : 0 < K) (μ : ℤ → ℝ)
    (S : Finset ℤ) (hsupp : ∀ z ∉ S, μ z = 0)
    (hnorm : ∑' z : ℤ, μ z = 1) :
    ∑ a : Fin K, integerResidueLaw K hK μ a = 1 := by
  classical
  have hres (z : ℤ) :
      ∑ a : Fin K, (if FromArithmetic.integerResidue K hK z = a then 1 else 0) = 1 := by
    simp [Finset.sum_ite_eq']
  calc
    ∑ a : Fin K, integerResidueLaw K hK μ a =
        ∑ a : Fin K, ∑ z ∈ S,
          μ z * (if FromArithmetic.integerResidue K hK z = a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold integerResidueLaw
      rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
        (f := fun z => μ z * (if FromArithmetic.integerResidue K hK z = a then 1 else 0))
        (s := S) (by intro z hz; simp [hsupp z hz])]
    _ = ∑ z ∈ S, μ z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      calc
        (∑ a : Fin K, μ z *
            (if FromArithmetic.integerResidue K hK z = a then 1 else 0)) =
          μ z * ∑ a : Fin K,
            (if FromArithmetic.integerResidue K hK z = a then 1 else 0) := by
          rw [Finset.mul_sum]
        _ = μ z * 1 := by
          congr 1
          simpa using hres z
        _ = μ z := by ring
    _ = 1 := by
      rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ) (f := μ) (s := S) hsupp]
      exact hnorm

theorem integerResidueLaw_eq_harmonicResidueLaw_of_nonneg_support {K : ℕ}
    (hK : 0 < K) (μ : ℤ → ℝ) (hμ : ∀ z, ¬ 0 ≤ z → μ z = 0) :
    integerResidueLaw K hK μ = harmonicResidueLaw μ K := by
  classical
  funext a
  unfold integerResidueLaw harmonicResidueLaw
  apply tsum_congr
  intro z
  by_cases hz : 0 ≤ z
  · have hres : FromArithmetic.integerResidue K hK z =
        ⟨z.toNat % K, Nat.mod_lt _ hK⟩ := by
      apply Fin.ext
      have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
      have hrem : z % (K : ℤ) = ((z.toNat % K : ℕ) : ℤ) := by
        calc
          z % (K : ℤ) = (z.toNat : ℤ) % (K : ℤ) :=
            congrArg (fun t : ℤ => t % (K : ℤ)) hcast.symm
          _ = ((z.toNat % K : ℕ) : ℤ) :=
            by
              simpa only [Int.toNat_natCast] using
                (Int.natCast_mod (m := z.toNat) (n := K)).symm
      have hval : (z % (K : ℤ)).toNat = z.toNat % K := by
        have h := congrArg Int.toNat hrem
        simpa only [Int.toNat_natCast] using h
      change (z % (K : ℤ)).toNat = z.toNat % K
      exact hval
    rw [hres]
    simp [hz, Fin.ext_iff]
  · have hzero : μ z = 0 := hμ z hz
    simp [hz, hzero]

theorem integerResidueLaw_uniformInterval_eq_nat {K T : ℕ} (hK : 0 < K) (hT : 0 < T) :
    integerResidueLaw K hK (FromArithmetic.uniformIntegerIntervalLaw 0 T) =
      fun a : Fin K =>
        ∑ n ∈ Finset.Ico 0 T,
          if n % K = a.val then 1 / (T : ℝ) else 0 := by
  classical
  funext a
  let I : Finset ℤ := Finset.Ico 0 (T : ℤ)
  have hsupp : ∀ z ∉ I, FromArithmetic.uniformIntegerIntervalLaw 0 T z = 0 := by
    intro z hz
    unfold FromArithmetic.uniformIntegerIntervalLaw
    rw [if_neg]
    intro h
    exact hz (Finset.mem_Ico.mpr (by simpa using h))
  have hsupp' : ∀ z ∉ I,
      FromArithmetic.uniformIntegerIntervalLaw 0 T z *
        (if FromArithmetic.integerResidue K hK z = a then 1 else 0) = 0 := by
    intro z hz
    simp [hsupp z hz]
  unfold integerResidueLaw
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (f := fun z => FromArithmetic.uniformIntegerIntervalLaw 0 T z *
      (if FromArithmetic.integerResidue K hK z = a then 1 else 0))
    (s := I) hsupp']
  have himage :
      (Finset.Ico 0 T).image (fun n : ℕ => (n : ℤ)) = I := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      have hn' := Finset.mem_Ico.mp hn
      simp [I, Finset.mem_Ico, hn']
    · intro hz
      have hz' := Finset.mem_Ico.mp (by simpa [I] using hz)
      have hnonneg : 0 ≤ z := hz'.1
      have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hnonneg
      have hlt : z.toNat < T := by
        have hltZ : (z.toNat : ℤ) < (T : ℤ) := by
          simpa [hcast] using hz'.2
        exact_mod_cast hltZ
      apply Finset.mem_image.mpr
      refine ⟨z.toNat, Finset.mem_Ico.mpr ?_, hcast⟩
      exact ⟨by omega, hlt⟩
  rw [← himage]
  rw [Finset.sum_image (s := Finset.Ico 0 T)
    (g := fun n : ℕ => (n : ℤ))
    (f := fun z : ℤ => FromArithmetic.uniformIntegerIntervalLaw 0 T z *
      (if FromArithmetic.integerResidue K hK z = a then 1 else 0))
    (by intro n hn m hm hnm; exact Int.ofNat.inj hnm)]
  apply Finset.sum_congr rfl
  intro n hn
  have hres : FromArithmetic.integerResidue K hK (n : ℤ) =
      ⟨n % K, Nat.mod_lt _ hK⟩ := by
    apply Fin.ext
    have hrem : (n : ℤ) % (K : ℤ) = ((n % K : ℕ) : ℤ) :=
      (Int.natCast_mod (m := n) (n := K)).symm
    have hval : ((n : ℤ) % (K : ℤ)).toNat = n % K := by
      have h := congrArg Int.toNat hrem
      simpa only [Int.toNat_natCast] using h
    change ((n : ℤ) % (K : ℤ)).toNat = n % K
    exact hval
  simp [FromArithmetic.uniformIntegerIntervalLaw, hres, Finset.mem_Ico.mp hn, Fin.ext_iff]

theorem uniformIntegerInterval_residue_tv {K T : ℕ} (hK : 0 < K) (hT : 0 < T) :
    finiteL1 (integerResidueLaw K hK (FromArithmetic.uniformIntegerIntervalLaw 0 T))
      (uniformResidueLaw K) ≤ 2 * (K : ℝ) / T := by
  rw [integerResidueLaw_uniformInterval_eq_nat hK hT]
  simpa using FromArithmetic.uniform_interval_sampling_bounds 0 T K hT hK

theorem harmonic_cutoff_log_condition {X W : ℕ} (hW : 0 < W) (hX : 4 * W ≤ X) :
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

theorem masterScaleV_ge_primorial {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (l : Fin n) :
    primorial (N + 1) ≤ masterScaleV A N l := by
  have hW : primorial (N + 1) ≤ A.M N := A.Wle N
  unfold masterScaleV
  omega

theorem pkgElim_masterScaleV_ge_modulus {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (l : Fin n) :
    A.M N ≤ masterScaleV A N l := by
  unfold masterScaleV
  omega

theorem pkgElim_masterScaleV_tendsto {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l : Fin n) :
    Tendsto (fun N => (masterScaleV A N l : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun N : ℕ => (2 : ℝ) ^ (N + 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  apply tendsto_atTop_mono' atTop _ hpow
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hWdiv : 2 ∣ primorial (N + 1) := by
    apply (Nat.Prime.dvd_primorial_iff Nat.prime_two).2
    omega
  have hW : 2 ≤ primorial (N + 1) :=
    Nat.le_of_dvd (primorial_pos _) hWdiv
  have hpowNat : 2 ^ (N + 1) ≤ primorial (N + 1) ^ (N + 1) :=
    Nat.pow_le_pow_left hW (N + 1)
  have hM : primorial (N + 1) ^ (N + 1) ≤ A.M N :=
    Nat.le_of_dvd (A.Mpos N) (A.Mdiv N)
  have hV : A.M N ≤ masterScaleV A N l := pkgElim_masterScaleV_ge_modulus A N l
  exact_mod_cast hpowNat.trans (hM.trans hV)

theorem microcellDominates_trans {A B S : ℕ → ℝ}
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
    have hmul : (S n) ^ C ≤ B n := by
      simpa using (le_div_iff₀ hpow).mp hbs
    exact lt_of_lt_of_le hpow hmul
  have hfactor : A n / (S n) ^ C = (A n / B n) * (B n / (S n) ^ C) := by
    field_simp [ne_of_gt hBpos, ne_of_gt hpow]
  rw [hfactor]
  calc
    B n / (S n) ^ C ≤ (A n / B n) * (B n / (S n) ^ C) :=
      by
        simpa using
          (mul_le_mul_of_nonneg_right hab
            (le_of_lt (lt_of_lt_of_le zero_lt_one hbs)))
    _ = _ := rfl

theorem microcellDominates_mono {A B S : ℕ → ℝ}
    (hle : ∀ᶠ n in atTop, A n ≤ B n)
    (hS : ∀ᶠ n in atTop, 0 < S n)
    (hA : OAI.MicrocellScale.Dominates A S) :
    OAI.MicrocellScale.Dominates B S := by
  intro C hC
  apply tendsto_atTop_mono' atTop _ (hA C hC)
  filter_upwards [hle, hS] with n hn hSn
  exact div_le_div_of_nonneg_right hn
    (le_of_lt (Real.rpow_pos_of_pos hSn C))

theorem chainPivot_log_dominates_poolSize {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (k : Fin m) :
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (S.core.parameters.X N (C.block k).1 : ℝ))
      (fun N => ((S.primeStage.pool N C.gap).upper +
        masterScaleV S.core.parameters N C.gap : ℝ)) := by
  let T : ℕ → ℝ := fun N =>
    (S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap
  have hgap := S.gapStage.gap_dominates_pool_and_bound C.gap
  have hle : ∀ᶠ N in atTop,
      (S.core.parameters.H N C.gap : ℝ) ≤
        (S.core.parameters.H N (C.block k).1 : ℝ) := by
    filter_upwards [] with N
    have hdvd := S.gapStage.earlier_gaps_divide N C.gap (C.block k).1
      (C.pivots_after_gap k)
    exact_mod_cast Nat.le_of_dvd (S.core.parameters.Hpos N (C.block k).1) hdvd
  have hTpos : ∀ᶠ N in atTop, 0 < T N := by
    filter_upwards [] with N
    have hV : 0 < masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      positivity
    dsimp [T]
    positivity
  have hpivot : OAI.MicrocellScale.Dominates
      (fun N => (S.core.parameters.H N (C.block k).1 : ℝ)) T :=
    microcellDominates_mono hle hTpos hgap
  exact microcellDominates_trans
    (S.gapStage.raw_cutoff_log_dominates_gap (C.block k).1) hpivot hTpos

theorem chainPivot_nat_dominates_poolSize {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (k : Fin m) :
    OAI.MicrocellScale.Dominates
      (fun N => (S.core.parameters.X N (C.block k).1 : ℝ))
      (fun N => ((S.primeStage.pool N C.gap).upper +
        masterScaleV S.core.parameters N C.gap : ℝ)) := by
  let T : ℕ → ℝ := fun N =>
    (S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap
  have hTpos : ∀ᶠ N in atTop, 0 < T N := by
    filter_upwards [] with N
    have hV : 0 < masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      positivity
    dsimp [T]
    positivity
  have hlogle : ∀ᶠ N in atTop,
      Real.log (S.core.parameters.X N (C.block k).1 : ℝ) ≤
        (S.core.parameters.X N (C.block k).1 : ℝ) := by
    filter_upwards [] with N
    have hX := S.gapStage.valid_raw_cutoffs N (C.block k).1
    have hWpos : 0 < primorial (N + 1) := primorial_pos _
    have hXnat : 0 < S.core.parameters.X N (C.block k).1 := by
      have hbase : 0 < 4 * primorial (N + 1) := by positivity
      omega
    have hXpos : 0 ≤ (S.core.parameters.X N (C.block k).1 : ℝ) := by
      exact_mod_cast hXnat.le
    exact Real.log_le_self hXpos
  exact microcellDominates_mono hlogle hTpos
    (chainPivot_log_dominates_poolSize S C k)

theorem microcellDominates_of_eventually_le_pow {A T U : ℕ → ℝ} (q : ℕ)
    (hA : OAI.MicrocellScale.Dominates A T)
    (hT : ∀ᶠ n in atTop, 2 ≤ T n)
    (hUpos : ∀ᶠ n in atTop, 0 < U n)
    (hU : ∀ᶠ n in atTop, U n ≤ (T n) ^ (q + 3 : ℕ)) :
    OAI.MicrocellScale.Dominates A U := by
  intro C hC
  let C' : ℝ := C * ((q + 3 : ℕ) : ℝ)
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hAt := hA C' hC'
  apply tendsto_atTop_mono' atTop _ hAt
  filter_upwards [hAt.eventually_ge_atTop (1 : ℝ), hT, hUpos, hU]
    with n hAdiv hTn hUnpos hUn
  have hTpos : 0 < T n := by linarith
  have hUreal : U n ≤ (T n) ^ ((q + 3 : ℕ) : ℝ) := by
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
    have hmul : (T n) ^ C' ≤ A n := by
      simpa using (le_div_iff₀ hDen).mp hAdiv
    exact le_trans (le_of_lt (Real.rpow_pos_of_pos hTpos C')) hmul
  have hcomp : A n / (T n) ^ C' ≤ A n / (U n) ^ C := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hDen (Real.rpow_pos_of_pos hUnpos C)).2 hUto) hApos
  exact hcomp

theorem samplingScale_envelope_le_poolPow (P V W q : ℕ)
    (hW : W ≤ V) (hV : 2 ≤ V) :
    2 + W + V ^ q + 1 + V ≤ (P + V) ^ (q + 3) := by
  let T := P + V
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hVle : V ≤ T := by dsimp [T]; omega
  have hWle : W ≤ T := le_trans hW hVle
  have hpow : V ^ q ≤ T ^ q := Nat.pow_le_pow_left hVle q
  have hpowPos : 1 ≤ T ^ q := Nat.one_le_pow q T (by omega)
  have hT2 : 4 ≤ T ^ 2 := by
    have h := Nat.pow_le_pow_left hT 2
    norm_num at h ⊢
    exact h
  have hT3 : 4 * T ≤ T ^ 3 := by
    calc
      4 * T ≤ T ^ 2 * T := Nat.mul_le_mul_right T hT2
      _ = T ^ 3 := by ring_nf
  have hdiff : 2 * T + 3 ≤ T ^ 3 - 1 := by omega
  have hextra : 2 * T + 3 ≤ T ^ q * (T ^ 3 - 1) := by
    calc
      _ ≤ T ^ 3 - 1 := hdiff
      _ = 1 * (T ^ 3 - 1) := by simp
      _ ≤ T ^ q * (T ^ 3 - 1) := Nat.mul_le_mul_right _ hpowPos
  have hcombine : T ^ q + 2 * T + 3 ≤ T ^ q * T ^ 3 := by
    have hT3pos : 1 ≤ T ^ 3 := by omega
    have hmul : T ^ q * (T ^ 3 - 1) = T ^ q * T ^ 3 - T ^ q := by
      rw [Nat.mul_sub_left_distrib]
      simp
    omega
  calc
    2 + W + V ^ q + 1 + V ≤ T ^ q + 2 * T + 3 := by omega
    _ ≤ T ^ q * T ^ 3 := hcombine
    _ = T ^ (q + 3) := by rw [← Nat.pow_add]
    _ = (P + V) ^ (q + 3) := by rfl

theorem chainPivot_harmonicResidueError_superpoly {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (k : Fin m) :
    SuperPolynomialSmall
      (fun N => FromArithmetic.harmonicResidueUniformError
        (S.core.parameters.X N (C.block k).1) (primorial (N + 1))
        (masterScaleV S.core.parameters N C.gap ^ q))
      (fun N => (masterScaleV S.core.parameters N C.gap : ℝ)) := by
  classical
  let V : ℕ → ℕ := fun N => masterScaleV S.core.parameters N C.gap
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let Kseq : ℕ → ℕ := fun N => V N ^ q
  let H : ℕ → ℕ := fun _ => 1
  let X : ℕ → ℕ := fun N => S.core.parameters.X N (C.block k).1
  let T : ℕ → ℝ := fun N =>
    ((S.primeStage.pool N C.gap).upper + V N : ℝ)
  let U : ℕ → ℝ := fun N =>
    ((2 + W N + Kseq N + H N + V N : ℕ) : ℝ)
  have hV : ∀ N, 2 ≤ V N := by
    intro N
    dsimp [V, masterScaleV]
    omega
  have hWle : ∀ N, W N ≤ V N := by
    intro N
    exact masterScaleV_ge_primorial S.core.parameters N C.gap
  have hT : ∀ N, 2 ≤ T N := by
    intro N
    dsimp [T, V]
    have : 2 ≤ masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      omega
    exact_mod_cast le_trans this (Nat.le_add_left _ _)
  have hUpos : ∀ᶠ N in atTop, 0 < U N := by
    filter_upwards [] with N
    dsimp [U, W, Kseq, H]
    positivity
  have hUle : ∀ᶠ N in atTop, U N ≤ T N ^ (q + 3) := by
    filter_upwards [] with N
    dsimp [U, W, Kseq, H, T, V]
    exact_mod_cast samplingScale_envelope_le_poolPow
      ((S.primeStage.pool N C.gap).upper)
      (masterScaleV S.core.parameters N C.gap) (primorial (N + 1)) q
      (hWle N) (hV N)
  have hXDom : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ)) U :=
    microcellDominates_of_eventually_le_pow q
      (chainPivot_nat_dominates_poolSize S C k)
      (Filter.Eventually.of_forall hT) hUpos hUle
  have hK : ∀ N, 1 ≤ Kseq N := by
    intro N
    dsimp [Kseq, V]
    exact Nat.one_le_pow q _ (by unfold masterScaleV; omega)
  have hH : ∀ N, 1 ≤ H N := by intro N; simp [H]
  have hVpos : ∀ N, 1 ≤ V N := by
    intro N
    exact le_trans (by omega : 1 ≤ 2) (hV N)
  have hW : ∀ N, W N = primorial (N + 1) := by intro N; rfl
  have hX2 : ∀ᶠ N in atTop, 2 ≤ X N := by
    filter_upwards [] with N
    dsimp [X]
    have hcut := S.gapStage.valid_raw_cutoffs N (C.block k).1
    have hWpos : 0 < primorial (N + 1) := primorial_pos _
    omega
  have hden : ∀ᶠ N in atTop, Real.log (X N : ℝ) > (W N : ℝ) / X N := by
    filter_upwards [] with N
    dsimp [X, W]
    exact harmonic_cutoff_log_condition (primorial_pos _) 
      (S.gapStage.valid_raw_cutoffs N (C.block k).1)
  have hXDom' : OAI.MicrocellScale.Dominates (fun N => (X N : ℝ))
      (fun N => 2 + (W N : ℝ) + (Kseq N : ℝ) + (H N : ℝ) + (V N : ℝ)) := by
    simpa [U, Nat.cast_add, Nat.cast_one, add_assoc] using hXDom
  let Ulog : ℕ → ℝ := fun N =>
    ((2 + W N + Kseq N + V N : ℕ) : ℝ)
  have hUlogpos : ∀ᶠ N in atTop, 0 < Ulog N := by
    filter_upwards [] with N
    dsimp [Ulog]
    positivity
  have hUlogleU : ∀ N, Ulog N ≤ U N := by
    intro N
    dsimp [Ulog, U, H]
    exact_mod_cast (by omega : 2 + W N + Kseq N + V N ≤ 2 + W N + Kseq N + 1 + V N)
  have hUlogle : ∀ᶠ N in atTop, Ulog N ≤ T N ^ (q + 3 : ℕ) := by
    filter_upwards [hUle] with N hN
    exact le_trans (hUlogleU N) hN
  have hlogDom' : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
      Ulog :=
    microcellDominates_of_eventually_le_pow q
      (chainPivot_log_dominates_poolSize S C k)
      (Filter.Eventually.of_forall hT) hUlogpos hUlogle
  have hlogDom'' : OAI.MicrocellScale.Dominates (fun N => Real.log (X N : ℝ))
      (fun N => 2 + (W N : ℝ) + (Kseq N : ℝ) + (V N : ℝ)) := by
    simpa [Ulog, Nat.cast_add, add_assoc] using hlogDom'
  have hsample := FromArithmetic.sampling_asymptotics W Kseq H V X
    hK hH hVpos hW hX2 hden hXDom' hlogDom''
  simpa [V, W, Kseq, FromArithmetic.harmonicResidueUniformError] using hsample.1

theorem nat_div_lower_from_dominance {H T : ℕ → ℕ}
    (hT : ∀ᶠ N in atTop, 1 ≤ T N)
    (hDom : OAI.MicrocellScale.Dominates (fun N => (H N : ℝ)) (fun N => (T N : ℝ)))
    (J B q : ℕ) (hJ : 0 < J) :
    ∀ᶠ N in atTop, T N ^ q ≤ H N / (J * T N ^ B) := by
  have hExp : 0 < (q + B + 1 : ℝ) := by positivity
  have hratio := hDom (q + B + 1 : ℝ) hExp
  filter_upwards [hratio.eventually_ge_atTop (J : ℝ), hT] with N hN hTN
  have hTpos : 0 < (T N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hTN)
  have hpowPos : 0 < (T N : ℝ) ^ (q + B + 1 : ℝ) :=
    Real.rpow_pos_of_pos hTpos _
  have hmul : (J : ℝ) * (T N : ℝ) ^ (q + B + 1 : ℝ) ≤ H N :=
    (le_div_iff₀ hpowPos).mp hN
  have hmulNat : J * T N ^ (q + B + 1) ≤ H N := by
    have hmulR : (J : ℝ) * (T N : ℝ) ^ ((q + B + 1 : ℕ) : ℝ) ≤ (H N : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hmul
    exact_mod_cast hmulR
  have hpowle : T N ^ (q + B) ≤ T N ^ (q + B + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hTN)
  have hprod : (T N ^ q) * (J * T N ^ B) ≤ H N := by
    calc
      _ = J * T N ^ (q + B) := by
        rw [pow_add]
        ac_rfl
      _ ≤ J * T N ^ (q + B + 1) := Nat.mul_le_mul_left J hpowle
      _ ≤ H N := hmulNat
  have hTposNat : 0 < T N := Nat.lt_of_lt_of_le Nat.zero_lt_one hTN
  have hDenNat : 0 < J * T N ^ B := Nat.mul_pos hJ (Nat.pow_pos hTposNat)
  exact (Nat.le_div_iff_mul_le hDenNat).2 hprod

theorem nat_div_denominator_dominates_scale {H T : ℕ → ℕ}
    (hT1 : ∀ᶠ N in atTop, 1 ≤ T N)
    (hTatTop : Tendsto (fun N => (T N : ℝ)) atTop atTop)
    (hDom : OAI.MicrocellScale.Dominates (fun N => (H N : ℝ)) (fun N => (T N : ℝ)))
    (J B : ℕ) (hJ : 0 < J) :
    OAI.MicrocellScale.Dominates
      (fun N => ((H N / (J * T N ^ B) : ℕ) : ℝ)) (fun N => (T N : ℝ)) := by
  intro C hC
  obtain ⟨q, hq⟩ := exists_nat_gt (C + 1)
  have hdiv := nat_div_lower_from_dominance hT1 hDom J B q hJ
  apply tendsto_atTop_mono' atTop _ hTatTop
  filter_upwards [hT1, hdiv] with N hTN hdivN
  have hTpos : 0 < (T N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hTN
  have hTpowPos : 0 < (T N : ℝ) ^ C := Real.rpow_pos_of_pos hTpos C
  have hdivR : (T N : ℝ) ^ q ≤ ((H N / (J * T N ^ B) : ℕ) : ℝ) := by
    exact_mod_cast hdivN
  have hdivR' : (T N : ℝ) ^ (q : ℝ) ≤ ((H N / (J * T N ^ B) : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using hdivR
  have hpowle : (T N : ℝ) ^ (C + 1) ≤ (T N : ℝ) ^ (q : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hTN) (le_of_lt hq)
  have hsplit : (T N : ℝ) ^ (C + 1) = (T N : ℝ) ^ C * T N := by
    rw [Real.rpow_add hTpos C 1]
    simp
  have hmul : (T N : ℝ) ^ C * T N ≤
      ((H N / (J * T N ^ B) : ℕ) : ℝ) := by
    calc
      _ = (T N : ℝ) ^ (C + 1) := hsplit.symm
      _ ≤ (T N : ℝ) ^ (q : ℝ) := hpowle
      _ ≤ _ := hdivR'
  have hlen : (T N : ℝ) ≤
      ((H N / (J * T N ^ B) : ℕ) : ℝ) / (T N : ℝ) ^ C := by
    exact (le_div_iff₀ hTpowPos).2 (by simpa [mul_comm] using hmul)
  exact hlen

theorem microcellDominates_ratio_superPolynomial {H T : ℕ → ℕ}
    (hT : ∀ᶠ N in atTop, 1 ≤ (T N : ℝ))
    (hDom : OAI.MicrocellScale.Dominates (fun N => (H N : ℝ)) (fun N => (T N : ℝ)))
    (q : ℕ) :
    SuperPolynomialSmall (fun N => (T N : ℝ) ^ q / H N) (fun N => (T N : ℝ)) := by
  intro C hC
  let E : ℝ := (q : ℝ) + C + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hratio := hDom E hE
  have hInv : Tendsto (fun N => ((H N : ℝ) / (T N : ℝ) ^ E)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hratio
  have hEq : (fun N => ((H N : ℝ) / (T N : ℝ) ^ E)⁻¹) =ᶠ[atTop]
      fun N => (T N : ℝ) ^ E / H N := by
    filter_upwards [hT, hratio.eventually_ge_atTop (1 : ℝ)] with N hTN hHN
    have hTpos : 0 < (T N : ℝ) := by linarith
    have hpow : 0 < (T N : ℝ) ^ E := Real.rpow_pos_of_pos hTpos E
    have hHpos : 0 < (H N : ℝ) := by
      have hmul := (le_div_iff₀ hpow).mp hHN
      linarith
    field_simp
  have hUpper : Tendsto (fun N => (T N : ℝ) ^ E / H N) atTop (𝓝 0) :=
    (tendsto_congr' hEq).1 hInv
  have hRatioOne : ∀ᶠ N in atTop, 1 ≤ (H N : ℝ) / (T N : ℝ) ^ E :=
    hratio.eventually_ge_atTop 1
  have hHpos : ∀ᶠ N in atTop, 0 < (H N : ℝ) := by
    filter_upwards [hT, hRatioOne] with N hTN hHN
    have hTpos : 0 < (T N : ℝ) := by linarith
    have hpow : 0 < (T N : ℝ) ^ E := Real.rpow_pos_of_pos hTpos E
    have hmul : (T N : ℝ) ^ E ≤ H N := by
      simpa using (le_div_iff₀ hpow).mp hHN
    exact lt_of_lt_of_le hpow hmul
  have hle : ∀ᶠ N in atTop,
      ((T N : ℝ) ^ q / H N) * (T N : ℝ) ^ C ≤ (T N : ℝ) ^ E / H N := by
    filter_upwards [hT, hHpos] with N hTN hHN
    have hTpos : 0 < (T N : ℝ) := by linarith
    have hpowEq : (T N : ℝ) ^ q * (T N : ℝ) ^ C =
        (T N : ℝ) ^ ((q : ℝ) + C) := by
      calc
        _ = (T N : ℝ) ^ (q : ℝ) * (T N : ℝ) ^ C := by rw [← Real.rpow_natCast]
        _ = _ := (Real.rpow_add hTpos (q : ℝ) C).symm
    have hpowle : (T N : ℝ) ^ ((q : ℝ) + C) ≤ (T N : ℝ) ^ E := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hTN
      · dsimp [E]
        linarith
    have hpowle' : (T N : ℝ) ^ q * (T N : ℝ) ^ C ≤ (T N : ℝ) ^ E := by
      rw [hpowEq]
      exact hpowle
    have hquot :
        ((T N : ℝ) ^ q * (T N : ℝ) ^ C) / H N ≤ (T N : ℝ) ^ E / H N :=
      div_le_div_of_nonneg_right hpowle' hHN.le
    calc
      _ = ((T N : ℝ) ^ q * (T N : ℝ) ^ C) / H N := by ring
      _ = _ := by rw [hpowEq]
      _ ≤ _ := hquot
  apply squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) hle hUpper


theorem intervalResidueError_superpoly_of_dominance {H T : ℕ → ℕ}
    (hT1 : ∀ᶠ N in atTop, 1 ≤ T N)
    (hTatTop : Tendsto (fun N => (T N : ℝ)) atTop atTop)
    (hDom : OAI.MicrocellScale.Dominates (fun N => (H N : ℝ)) (fun N => (T N : ℝ)))
    (J B q : ℕ) (hJ : 0 < J) :
    SuperPolynomialSmall
      (fun N => 2 * (T N : ℝ) ^ q / (H N / (J * T N ^ B) : ℕ))
      (fun N => (T N : ℝ)) := by
  have hmin := nat_div_denominator_dominates_scale hT1 hTatTop hDom J B hJ
  intro C hC
  have hT1R : ∀ᶠ N in atTop, 1 ≤ (T N : ℝ) := by
    filter_upwards [hT1] with N hN
    exact_mod_cast hN
  convert (microcellDominates_ratio_superPolynomial hT1R hmin q C hC).const_mul
    (2 : ℝ) using 1 <;> ext N <;> ring

theorem roughPart_pos (w : ℕ) (a : ℤ) : 0 < roughPart w a := by
  classical
  unfold roughPart
  apply Finset.prod_pos
  intro p hp
  exact Nat.pow_pos ((Finset.mem_filter.mp hp).2.1.pos)

theorem shiftLength_lower_pow_of_modulus_bound {K s m r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (J0 B q : ℕ)
    (hJ0 : 0 < J0) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q))
    (hbound : ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      directionModulus S N dirs.poly p ≤
        ((S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap) ^ B) :
    ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      ((S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap) ^ q ≤
        shiftLength S C.gap J0 N dirs.poly p := by
  classical
  let H : ℕ → ℕ := fun N => S.core.parameters.H N C.gap
  let T : ℕ → ℕ := fun N =>
    (S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap
  have hT : ∀ N, 1 ≤ T N := by
    intro N
    dsimp [T]
    have hV : 2 ≤ masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      omega
    omega
  have hscale : OAI.MicrocellScale.Dominates (fun N => (H N : ℝ)) (fun N => (T N : ℝ)) := by
    simpa [H, T] using S.gapStage.gap_dominates_pool_and_bound C.gap
  have hlarge := nat_div_lower_from_dominance
    (Filter.Eventually.of_forall hT) hscale J0 B q hJ0
  have hMpos (N : ℕ) (p : Fin q → ℕ) :
      0 < directionModulus S N dirs.poly p := by
    unfold directionModulus
    exact Nat.mul_pos (S.core.parameters.Mpos N) (roughPart_pos _ _)
  filter_upwards [hlarge, hbound] with N hlargeN hboundN p hp
  let Mp := directionModulus S N dirs.poly p
  have hTnat : T N =
      (S.primeStage.pool N C.gap).upper + masterScaleV S.core.parameters N C.gap := rfl
  have hTpos : 0 < T N := Nat.lt_of_lt_of_le Nat.zero_lt_one (hT N)
  have hdenMaxPos : 0 < J0 * T N ^ B := Nat.mul_pos hJ0 (Nat.pow_pos hTpos)
  have hprodMax : T N ^ q * (J0 * T N ^ B) ≤ H N :=
    (Nat.le_div_iff_mul_le hdenMaxPos).mp (hlargeN)
  have hdenLe : J0 * Mp ≤ J0 * T N ^ B :=
    Nat.mul_le_mul_left J0 (hboundN p hp)
  have hprod : T N ^ q * (J0 * Mp) ≤ H N :=
    le_trans (Nat.mul_le_mul_left (T N ^ q) hdenLe) hprodMax
  have hdenPos : 0 < J0 * Mp := Nat.mul_pos hJ0 (hMpos N p)
  have hlen : T N ^ q ≤ H N / (J0 * Mp) :=
    (Nat.le_div_iff_mul_le hdenPos).2 hprod
  simpa [shiftLength, Mp, H, T, hTnat] using hlen

theorem harmonicIntegerResidueLaw_tv {X W K : ℕ}
    (hW : 0 < W) (hX : 2 ≤ X) (hlog : Real.log X > (W : ℝ) / X)
    (hcop : Nat.Coprime K W) (hK : 0 < K) :
    finiteL1 (integerResidueLaw K hK (harmonicLaw X W)) (uniformResidueLaw K) ≤
      FromArithmetic.harmonicResidueError X W K := by
  have hnonnegSupport : ∀ z, ¬ 0 ≤ z → harmonicLaw X W z = 0 := by
    intro z hz
    simp [harmonicLaw, hz]
  rw [integerResidueLaw_eq_harmonicResidueLaw_of_nonneg_support hK
    (harmonicLaw X W) hnonnegSupport]
  exact (FromArithmetic.sampling_pointwise_claim X W hW hX hlog).residue_total_mass
    hX hlog K hcop hK

set_option maxHeartbeats 500000 in
theorem productBaseResidueLaw_finiteL1_le {d K : ℕ} (hK : 0 < K)
    (μ : Fin d → ℤ → ℝ) (S : Fin d → Finset ℤ)
    (hsupp : ∀ i z, z ∉ S i → μ i z = 0) (r : Fin d → Fin K)
    (hcoord_nonneg : ∀ i a, 0 ≤ integerResidueLaw K hK (μ i) a)
    (hcoord_norm : ∀ i, ∑ a, integerResidueLaw K hK (μ i) a = 1)
    (ε : Fin d → ℝ)
    (hcoord_error : ∀ i,
      finiteL1 (integerResidueLaw K hK (μ i)) (uniformResidueLaw K) ≤ ε i) :
    finiteL1
      (FromArithmetic.baseResidueLaw K hK (fun x => ∏ i, μ i (x i)))
      (FromArithmetic.uniformBaseResidueLaw K d) ≤ ∑ i, ε i := by
  classical
  letI : Fintype (Fin d → Fin K) := Pi.instFintype
  have hbase : FromArithmetic.baseResidueLaw K hK (fun x => ∏ i, μ i (x i)) =
      fun r => ∏ i, integerResidueLaw K hK (μ i) (r i) := by
    funext r
    exact productBaseResidueLaw_eq_product hK μ S hsupp r
  have huniform : FromArithmetic.uniformBaseResidueLaw K d =
      fun r => ∏ i, uniformResidueLaw K (r i) := by
    funext r
    simp [FromArithmetic.uniformBaseResidueLaw, uniformResidueLaw, Finset.prod_const,
      one_div, pow_mul]
  let μ' : Fin d → Fin K → ℝ := fun i => integerResidueLaw K hK (μ i)
  let ν' : Fin d → Fin K → ℝ := fun _ a => uniformResidueLaw K a
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hνpos : ∀ i a, 0 ≤ ν' i a := by
    intro i a
    simpa [ν', uniformResidueLaw] using
      (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hKr.le)
  have hνnorm : ∀ i, ∑ a, ν' i a = 1 := by
    intro i
    calc
      ∑ a : Fin K, ν' i a = (K : ℝ) * (1 / (K : ℝ)) := by simp [ν', uniformResidueLaw]
      _ = 1 := by field_simp
  have hTV : finiteL1 (fun z : Fin d → Fin K => ∏ i, μ' i (z i))
      (fun z : Fin d → Fin K => ∏ i, ν' i (z i)) ≤ ∑ i, finiteL1 (μ' i) (ν' i) := by
    exact finiteL1_product_probability_le (ι := Fin d) (α := Fin K)
      (μ := μ') (ν := ν') hcoord_nonneg hνpos hcoord_norm hνnorm
  calc
    finiteL1
        (FromArithmetic.baseResidueLaw K hK (fun x => ∏ i, μ i (x i)))
        (FromArithmetic.uniformBaseResidueLaw K d) =
      finiteL1 (fun z : Fin d → Fin K => ∏ i, μ' i (z i))
        (fun z : Fin d → Fin K => ∏ i, ν' i (z i)) := by
        rw [hbase, huniform]
    _ ≤ ∑ i, finiteL1 (μ' i) (ν' i) := hTV
    _ ≤ ∑ i, ε i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcoord_error i

theorem pkgElim_pivotMass_tsum_one {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (hW : 0 < primorial (N + 1))
    (hX : ∀ k, 4 * primorial (N + 1) ≤ A.X N (C.block k).1) :
    ∑' z : Fin m → ℤ, pivotMass A C N z = 1 := by
  classical
  let S : Fin m → Finset ℤ := fun k =>
    (Finset.Ico (A.X N (C.block k).1) ((A.X N (C.block k).1) ^ 2)).image
      (fun z : ℕ => (z : ℤ))
  have hcoord (k : Fin m) :
      ∑ z ∈ S k, harmonicLaw (A.X N (C.block k).1) (primorial (N + 1)) z = 1 := by
    simpa [S] using harmonicLaw_sum_support hW (hX k)
  have hsupp (k : Fin m) (z : ℤ) (hz : z ∉ S k) :
      harmonicLaw (A.X N (C.block k).1) (primorial (N + 1)) z = 0 := by
    unfold harmonicLaw
    rw [if_neg]
    intro h
    apply hz
    refine Finset.mem_image.mpr ⟨z.toNat, Finset.mem_Ico.mpr ?_, ?_⟩
    · exact ⟨by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1⟩
    · exact Int.toNat_of_nonneg h.1
  unfold pivotMass
  exact productLaw_tsum_one_of_finite_support
    (μ := fun k z => harmonicLaw (A.X N (C.block k).1) (primorial (N + 1)) z)
    (S := S) (fun k z hz => hsupp k z hz) hcoord

def rowTemplateCoefficient {m q : ℕ} (c : Fin m → ℚ) (T : RowTemplate m q)
    (p : Fin q → ℕ) (k : Fin m) : ℚ :=
  c k / c T.anchor * T.value p k

theorem rowForm_eq_linearRowValue {m q r : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (p : Fin q → ℕ) (x : Fin m → ℤ)
    (N : ℕ) (u : Fin r) :
    rowForm c T p (fun k => (x k : ℚ)) =
      FromArithmetic.linearRowValue
        (fun _ p' _ k => rowTemplateCoefficient c T p' k) N p u x := by
  simp [rowForm, FromArithmetic.linearRowValue, rowTemplateCoefficient]

theorem pkgElim_rowTemplateValue_integer {m q : ℕ}
    (T : RowTemplate m q) (p : Fin q → ℕ) (k : Fin m) :
    ∃ z : ℤ, T.value p k = (z : ℚ) := by
  classical
  cases he : T.entry k with
  | none => exact ⟨0, by simp [RowTemplate.value, he]⟩
  | some e =>
    refine ⟨∏ i : Fin q, (p i : ℤ) ^ e i, ?_⟩
    simp [RowTemplate.value, he]

theorem pkgElim_rowTemplateCoefficient_integer {m q : ℕ}
    (T : RowTemplate m q) (p : Fin q → ℕ) (k : Fin m)
    (c : Fin m → ℚ) (cZ : Fin m → ℤ) (hc : ∀ j, c j = (cZ j : ℚ))
    (hcpos : ∀ j, 0 < cZ j) (W : ℕ)
    (hratio : ∀ u d, u < d → ∃ n : ℕ,
      cZ u = (W : ℤ) * (n : ℤ) * cZ d) :
    ∃ z : ℤ, rowTemplateCoefficient c T p k = (z : ℚ) := by
  classical
  have hanchorPos : 0 < cZ T.anchor := hcpos T.anchor
  have hanchorNe : (cZ T.anchor : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hanchorPos)
  have hcAnchorNe : c T.anchor ≠ 0 := by
    rw [hc T.anchor]
    exact hanchorNe
  obtain ⟨v, hv⟩ := pkgElim_rowTemplateValue_integer T p k
  cases he : T.entry k with
  | none => exact ⟨0, by simp [rowTemplateCoefficient, RowTemplate.value, he]⟩
  | some e =>
    have hmem : k ∈ T.support := by simp [RowTemplate.support, he]
    have hkle : k ≤ T.anchor := Finset.le_max' T.support k hmem
    by_cases heq : k = T.anchor
    · subst k
      refine ⟨v, ?_⟩
      unfold rowTemplateCoefficient
      rw [div_self hcAnchorNe, one_mul]
      exact hv
    · have hlt : k < T.anchor := lt_of_le_of_ne hkle heq
      obtain ⟨n, hn⟩ := hratio k T.anchor hlt
      have hscale : c k / c T.anchor = (W : ℚ) * n := by
        rw [hc k, hc T.anchor, hn]
        push_cast
        field_simp [hanchorNe]
      refine ⟨W * n * v, ?_⟩
      unfold rowTemplateCoefficient
      rw [hscale, hv]
      push_cast
      ring

theorem uniformIntegerIntervalLaw_tsum_one {L : ℕ} (hL : 0 < L) :
    ∑' z : ℤ, FromArithmetic.uniformIntegerIntervalLaw 0 L z = 1 := by
  classical
  let I : Finset ℤ := Finset.Ico 0 (L : ℤ)
  have hsupp : ∀ z ∉ I, FromArithmetic.uniformIntegerIntervalLaw 0 L z = 0 := by
    intro z hz
    unfold FromArithmetic.uniformIntegerIntervalLaw
    rw [if_neg]
    intro h
    exact hz (Finset.mem_Ico.mpr (by simpa using h))
  rw [tsum_eq_sum hsupp]
  have hcard : I.card = L := by
    have hcardZ : (I.card : ℤ) = (L : ℤ) := by
      dsimp [I]
      rw [Int.card_Ico_of_le 0 (L : ℤ) (by exact_mod_cast hL.le)]
      simp
    exact_mod_cast hcardZ
  calc
    (∑ z ∈ I, FromArithmetic.uniformIntegerIntervalLaw 0 L z) =
        ∑ z ∈ I, 1 / (L : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [FromArithmetic.uniformIntegerIntervalLaw, Finset.mem_Ico.mp hz]
    _ = (I.card : ℝ) * (1 / (L : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
      rw [hcard]
      have hLR : (0 : ℝ) < L := by exact_mod_cast hL
      field_simp

theorem uniformIntegerIntervalProduct_tsum_one {ι : Type*} [Fintype ι]
    (L : ℕ) (hL : 0 < L) :
    ∑' x : ι → ℤ, ∏ i, FromArithmetic.uniformIntegerIntervalLaw 0 L (x i) = 1 := by
  classical
  let I : ι → Finset ℤ := fun _ => Finset.Ico 0 (L : ℤ)
  have hsupp (i : ι) (z : ℤ) (hz : z ∉ I i) :
      FromArithmetic.uniformIntegerIntervalLaw 0 L z = 0 := by
    unfold FromArithmetic.uniformIntegerIntervalLaw
    rw [if_neg]
    intro h
    exact hz (Finset.mem_Ico.mpr (by simpa using h))
  have hnorm (i : ι) :
      ∑ z ∈ I i, FromArithmetic.uniformIntegerIntervalLaw 0 L z = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (f := FromArithmetic.uniformIntegerIntervalLaw 0 L) (s := I i)
      (hsupp i)]
    exact uniformIntegerIntervalLaw_tsum_one hL
  exact productLaw_tsum_one_of_finite_support
    (μ := fun _ z => FromArithmetic.uniformIntegerIntervalLaw 0 L z)
    (S := I) (fun i z hz => hsupp i z hz) hnorm

theorem shiftAverage_eq_uniformIntervalSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F : (ι → Fin 2 → ℕ) → ℝ) :
    shiftAverage ι L F =
      ∑ u ∈ Fintype.piFinset
          (fun _ : ι => Fintype.piFinset (fun _ : Fin 2 => Finset.range L)),
        (∏ i, ∏ j : Fin 2,
          FromArithmetic.uniformIntegerIntervalLaw 0 L (u i j : ℤ)) * F u := by
  classical
  let S : Finset (ι → Fin 2 → ℕ) := Fintype.piFinset
    (fun _ : ι => Fintype.piFinset (fun _ : Fin 2 => Finset.range L))
  have hweight (u : ι → Fin 2 → ℕ) (hu : u ∈ S) :
      (∏ i, ∏ j : Fin 2,
        FromArithmetic.uniformIntegerIntervalLaw 0 L (u i j : ℤ)) =
        ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ := by
    have hcoord (i : ι) (j : Fin 2) :
        FromArithmetic.uniformIntegerIntervalLaw 0 L (u i j : ℤ) = 1 / (L : ℝ) := by
      have hwhole : u ∈ Fintype.piFinset
          (fun _ : ι => Fintype.piFinset (fun _ : Fin 2 => Finset.range L)) := by
        simpa only [S] using hu
      have hi : u i ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range L) :=
        (Fintype.mem_piFinset.mp hwhole) i
      have hij : u i j ∈ Finset.range L := Fintype.mem_piFinset.mp hi j
      have hlt : u i j < L := Finset.mem_range.mp hij
      have hltZ : (u i j : ℤ) < (L : ℤ) := by exact_mod_cast hlt
      simp [FromArithmetic.uniformIntegerIntervalLaw, hltZ]
    calc
      _ = ∏ i, ∏ j : Fin 2, (1 / (L : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro j hj
        exact hcoord i j
      _ = ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ := by
        simp [Finset.prod_const, one_div, inv_pow, pow_mul]
  unfold shiftAverage
  change ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ *
      (∑ u ∈ S, F u) =
    ∑ u ∈ S,
      (∏ i, ∏ j : Fin 2,
        FromArithmetic.uniformIntegerIntervalLaw 0 L (u i j : ℤ)) * F u
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hweight u hu]

theorem pkgElim_primePoolLaw_tsum_one {lo hi : ℕ} (hmass : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  classical
  let s : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  have hsupp : ∀ p ∉ s, primePoolLaw lo hi p = 0 := by
    intro p hp
    unfold primePoolLaw
    rw [if_neg]
    intro h
    exact hp (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
  rw [tsum_eq_sum hsupp]
  have hsum :
      (∑ p ∈ s, 1 / (p : ℝ)) = primePoolMass lo hi := by
    rfl
  calc
    ∑ p ∈ s, primePoolLaw lo hi p =
        ∑ p ∈ s, (1 / (p : ℝ)) / primePoolMass lo hi := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hIco, hPrime⟩
      rcases Finset.mem_Ico.mp hIco with ⟨hlo, hhi⟩
      have hp' : lo ≤ p ∧ p < hi ∧ Nat.Prime p := ⟨hlo, hhi, hPrime⟩
      simp [primePoolLaw, hp'.1, hp'.2.1, hp'.2.2]
    _ = (∑ p ∈ s, 1 / (p : ℝ)) / primePoolMass lo hi := by
      rw [Finset.sum_div]
    _ = 1 := by rw [hsum]; exact div_self (ne_of_gt hmass)

theorem primeResidueIndicator_sum {Q p : ℕ} (hQ : 0 < Q) :
    (∑ a : Fin Q, if p % Q = a.val then 1 / (p : ℝ) else 0) = 1 / (p : ℝ) := by
  classical
  let a₀ : Fin Q := ⟨p % Q, Nat.mod_lt _ hQ⟩
  rw [Finset.sum_eq_single a₀]
  · simp [a₀]
  · intro a ha hne
    have hneq : p % Q ≠ a.val := by
      intro hv
      apply hne
      apply Fin.ext
      simpa [a₀] using hv.symm
    simp [hneq]
  · simp

theorem primePoolResidueLaw_sum_one {lo hi Q : ℕ}
    (hQ : 0 < Q) (hmass : 0 < primePoolMass lo hi) :
    (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) = 1 := by
  classical
  let S : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  calc
    (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) =
      (∑ a : Fin Q, ∑ p ∈ S,
        if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi := by
      unfold primePoolResidueLaw
      rw [Finset.sum_div]
    _ = (∑ p ∈ S, ∑ a : Fin Q,
        if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi := by
      rw [Finset.sum_comm]
    _ = (∑ p ∈ S, 1 / (p : ℝ)) / primePoolMass lo hi := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact primeResidueIndicator_sum hQ
    _ = 1 := by
      have hmassEq : (∑ p ∈ S, 1 / (p : ℝ)) = primePoolMass lo hi := by rfl
      rw [hmassEq]
      exact div_self (ne_of_gt hmass)

theorem finitePushforward_sum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (μ : α → ℝ) :
    (∑ b, finitePushforward f μ b) = ∑ a, μ a := by
  classical
  unfold finitePushforward
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

theorem finitePushforward_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) :
    ∀ b, 0 ≤ finitePushforward f μ b := by
  classical
  intro b
  unfold finitePushforward
  apply Finset.sum_nonneg
  intro a ha
  by_cases h : f a = b
  · simp [h, hμ a]
  · simp [h]

theorem uniformUnitResidueLaw_nonneg {Q : ℕ} (hQ : 0 < Q) (a : Fin Q) :
    0 ≤ uniformUnitResidueLaw Q a := by
  unfold uniformUnitResidueLaw
  split_ifs with h
  · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  · exact le_rfl

theorem pkgElim_primePoolLaw_nonneg {lo hi : ℕ} (hmass : 0 < primePoolMass lo hi) (p : ℕ) :
    0 ≤ primePoolLaw lo hi p := by
  unfold primePoolLaw
  split_ifs with hp
  · have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.2.2.pos
    exact div_nonneg (div_nonneg (by norm_num) hpPos.le) hmass.le
  · exact le_rfl

noncomputable def crtResidueProjection {w V Q : ℕ} (a : Fin Q) : FromArithmetic.CRTResidues w V :=
  fun p => ⟨a.val % p.val, Nat.mod_lt _ ((Finset.mem_filter.mp p.property).2.pos)⟩

theorem crtResidueProjection_mod {w V Q : ℕ} (hQ : 0 < Q)
    (hdiv : ∀ p : FromArithmetic.CRTPrimeRange w V, p.val ∣ Q) (n : ℕ) :
    crtResidueProjection (w := w) (V := V) (Q := Q) ⟨n % Q, Nat.mod_lt _ hQ⟩ =
      FromArithmetic.integerCRTResidues w V n := by
  classical
  funext p
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  apply Fin.ext
  simp [crtResidueProjection, FromArithmetic.integerCRTResidues,
    Nat.mod_mod_of_dvd n (hdiv p)]

theorem masterCRTModulus_mediumPrime_factorization {w e V p : ℕ}
    (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V + 1) :
    (FromArithmetic.masterCRTModulus w e V).factorization p = 1 := by
  classical
  let S := (Finset.Ioc w (V + 1)).filter Nat.Prime
  have hpS : p ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hwp, hpV⟩, hp⟩
  have hpnot : ¬ p ∣ primorial w := by
    intro hdiv
    have hle := (hp.dvd_primorial_iff).mp hdiv
    omega
  have hpow : (primorial w ^ e).factorization p = 0 := by
    rw [Nat.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd hpnot]
  have hprod : (∏ q ∈ S, q).factorization p = 1 := by
    rw [Nat.factorization_prod_apply (by
      intro q hq
      exact (Finset.mem_filter.mp hq).2.ne_zero)]
    calc
      _ = ∑ q ∈ S, if q = p then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqPrime := (Finset.mem_filter.mp hq).2
        rw [hqPrime.factorization]
        simp [Finsupp.single_apply]
      _ = 1 := by simp [Finset.sum_ite_eq', hpS]
  have hpowNe : primorial w ^ e ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt (primorial_pos w))
  have hprodNe : (∏ q ∈ S, q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact (Finset.mem_filter.mp hq).2.ne_zero
  unfold FromArithmetic.masterCRTModulus
  rw [Nat.factorization_mul hpowNe hprodNe, Finsupp.add_apply, hpow, hprod]

theorem masterCRTModulus_mediumPrime_dvd {w e V p : ℕ}
    (hp : p.Prime) (hwp : w < p) (hpV : p ≤ V + 1) :
    p ∣ FromArithmetic.masterCRTModulus w e V := by
  classical
  let S := (Finset.Ioc w (V + 1)).filter Nat.Prime
  have hpS : p ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hwp, hpV⟩, hp⟩
  have hprod : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q : ℕ => q) hpS
  unfold FromArithmetic.masterCRTModulus
  exact dvd_mul_of_dvd_right hprod _

theorem crtPrimeProduct_totient {w V : ℕ} :
    Nat.totient (∏ p : FromArithmetic.CRTPrimeRange w V, p.val) =
      ∏ p : FromArithmetic.CRTPrimeRange w V, (p.val - 1) := by
  classical
  let P : FromArithmetic.CRTPrimeRange w V → ℕ := fun p => p.val
  have hmain (s : Finset (FromArithmetic.CRTPrimeRange w V))
      (hprime : ∀ p ∈ s, (P p).Prime)
      (hpair : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → P p ≠ P q) :
      Nat.totient (∏ p ∈ s, P p) = ∏ p ∈ s, (P p - 1) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hps ih =>
      have hpr : (P p).Prime := hprime p (Finset.mem_insert_self _ _)
      have hprS : ∀ q ∈ s, (P q).Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hpairS : ∀ q ∈ s, ∀ r ∈ s, q ≠ r → P q ≠ P r := by
        intro q hq r hr hqr
        exact hpair q (Finset.mem_insert_of_mem hq)
          r (Finset.mem_insert_of_mem hr) hqr
      have hneVal : ∀ q ∈ s, P p ≠ P q := by
        intro q hq heq
        have hneq : p ≠ q := by
          intro hpq
          subst q
          exact hps hq
        exact (hpair p (Finset.mem_insert_self _ _)
          q (Finset.mem_insert_of_mem hq) hneq) heq
      have hcop : Nat.Coprime (P p) (∏ q ∈ s, P q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hpr (hprS q hq)).2 (hneVal q hq)
      rw [Finset.prod_insert hps, Nat.totient_mul hcop,
        Nat.totient_prime hpr, ih hprS hpairS, Finset.prod_insert hps]
  have hprime : ∀ p : FromArithmetic.CRTPrimeRange w V, (P p).Prime :=
    fun p => (Finset.mem_filter.mp p.property).2
  have hinj : Function.Injective P := by
    intro p q hpq
    exact Subtype.ext hpq
  simpa [P] using hmain Finset.univ (fun p hp => hprime p)
    (fun p hp q hq hne => by
      intro hval
      exact hne (hinj hval))

theorem masterCRTModulus_eq_base_mul_crtPrimeProduct {w e V : ℕ} :
    FromArithmetic.masterCRTModulus w e V =
      (primorial w ^ e) * (∏ p : FromArithmetic.CRTPrimeRange w V, p.val) := by
  classical
  let S := (Finset.Ioc w (V + 1)).filter Nat.Prime
  have hprod : (∏ p : FromArithmetic.CRTPrimeRange w V, p.val) = ∏ p ∈ S, p := by
    change (∏ p : S, (p : ℕ)) = ∏ p ∈ S, p
    exact Finset.prod_coe_sort S (fun p : ℕ => p)
  unfold FromArithmetic.masterCRTModulus
  rw [hprod]

theorem primorialPow_coprime_crtPrimeProduct {w e V : ℕ} (he : 0 < e) :
    Nat.Coprime (primorial w ^ e)
      (∏ p : FromArithmetic.CRTPrimeRange w V, p.val) := by
  classical
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  have hp' : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hwp : w < p.val := (Finset.mem_Ioc.mp
    (Finset.mem_filter.mp p.property).1).1
  have hnot : ¬p.val ∣ primorial w := by
    intro hdiv
    have hle := (hp'.dvd_primorial_iff).mp hdiv
    omega
  have hcop : Nat.Coprime p.val (primorial w) :=
    hp'.coprime_iff_not_dvd.mpr hnot
  exact (Nat.coprime_pow_left_iff he (primorial w) p.val).2 hcop.symm

theorem crtPrimeProduct_pairwise_coprime {w V : ℕ} :
    Pairwise (fun p q : FromArithmetic.CRTPrimeRange w V => Nat.Coprime p.val q.val) := by
  intro p q hpq
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hq : q.val.Prime := (Finset.mem_filter.mp q.property).2
  apply (Nat.coprime_primes hp hq).2
  intro hval
  apply hpq
  exact Subtype.ext hval

def masterCRTOptionFactor {w e V : ℕ}
    (i : Option (FromArithmetic.CRTPrimeRange w V)) : ℕ :=
  match i with
  | none => primorial w ^ e
  | some p => p.val

theorem masterCRTOptionFactor_pairwise {w e V : ℕ} (he : 0 < e) :
    Pairwise (Function.onFun Nat.Coprime (masterCRTOptionFactor (w := w) (e := e) (V := V))) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some p =>
      have hcop : Nat.Coprime (primorial w ^ e) p.val := by
        have h := (Nat.coprime_prod_right_iff.mp
          (primorialPow_coprime_crtPrimeProduct he)) p (Finset.mem_univ p)
        exact h
      simpa [Function.onFun, masterCRTOptionFactor] using hcop
  | some p =>
    cases j with
    | none =>
      have hcop : Nat.Coprime (primorial w ^ e) p.val := by
        have h := (Nat.coprime_prod_right_iff.mp
          (primorialPow_coprime_crtPrimeProduct he)) p (Finset.mem_univ p)
        exact h
      simpa [Function.onFun, masterCRTOptionFactor] using hcop.symm
    | some q =>
      have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
      have hq : q.val.Prime := (Finset.mem_filter.mp q.property).2
      have hpq : p.val ≠ q.val := by
        intro hv
        apply hij
        exact congrArg some (Subtype.ext hv)
      simpa [Function.onFun, masterCRTOptionFactor] using
        (Nat.coprime_primes hp hq).2 hpq

theorem masterCRTModulus_eq_optionFactorProduct {w e V : ℕ} :
    FromArithmetic.masterCRTModulus w e V =
      ∏ i : Option (FromArithmetic.CRTPrimeRange w V),
        masterCRTOptionFactor (w := w) (e := e) (V := V) i := by
  classical
  let F := masterCRTOptionFactor (w := w) (e := e) (V := V)
  have hoption : (∏ i : Option (FromArithmetic.CRTPrimeRange w V), F i) =
      F none * ∏ p : FromArithmetic.CRTPrimeRange w V, F (some p) := by
    have hU : (Finset.univ : Finset (Option (FromArithmetic.CRTPrimeRange w V))) =
        Finset.insertNone (Finset.univ : Finset (FromArithmetic.CRTPrimeRange w V)) := by
      ext i
      cases i <;> simp [Finset.insertNone]
    rw [hU, Finset.prod_insertNone]
  have hmod : FromArithmetic.masterCRTModulus w e V =
      ∏ i : Option (FromArithmetic.CRTPrimeRange w V), F i := by
    calc
      _ = (primorial w ^ e) *
          (∏ p : FromArithmetic.CRTPrimeRange w V, p.val) :=
        masterCRTModulus_eq_base_mul_crtPrimeProduct
      _ = F none * ∏ p : FromArithmetic.CRTPrimeRange w V, F (some p) := by
        simp [F, masterCRTOptionFactor]
      _ = _ := hoption.symm
  exact hmod

noncomputable def masterCRTModulus_optionPiRingEquiv {w e V : ℕ} (he : 0 < e) :
    ZMod (FromArithmetic.masterCRTModulus w e V) ≃+*
      (∀ i : Option (FromArithmetic.CRTPrimeRange w V),
        ZMod (masterCRTOptionFactor (w := w) (e := e) (V := V) i)) := by
  let F := masterCRTOptionFactor (w := w) (e := e) (V := V)
  exact (ZMod.ringEquivCongr masterCRTModulus_eq_optionFactorProduct).trans
    (ZMod.prodEquivPi F (masterCRTOptionFactor_pairwise he))

theorem masterCRTModulus_pos {w e V : ℕ} :
    0 < FromArithmetic.masterCRTModulus w e V := by
  rw [masterCRTModulus_eq_base_mul_crtPrimeProduct]
  apply Nat.mul_pos
  · exact pow_pos (primorial_pos w) e
  · apply Finset.prod_pos
    intro p hp
    exact (Finset.mem_filter.mp p.property).2.pos

theorem zmod_finEquiv_apply {n : ℕ} [NeZero n] (a : Fin n) :
    (ZMod.finEquiv n) a = (a.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    have hk : 0 < k + 1 := by omega
    change a = (⟨a.val % (k + 1), Nat.mod_lt _ hk⟩ : Fin (k + 1))
    apply Fin.ext
    exact (Nat.mod_eq_of_lt a.isLt).symm

noncomputable def crtOptionZModFinEquiv {w e V : ℕ}
    (i : Option (FromArithmetic.CRTPrimeRange w V)) :
    ZMod (masterCRTOptionFactor (w := w) (e := e) (V := V) i) ≃
      Fin (masterCRTOptionFactor (w := w) (e := e) (V := V) i) := by
  have hpos : 0 < masterCRTOptionFactor (w := w) (e := e) (V := V) i := by
    cases i with
    | none => exact pow_pos (primorial_pos w) e
    | some p => exact ((Finset.mem_filter.mp p.property).2).pos
  letI : NeZero (masterCRTOptionFactor (w := w) (e := e) (V := V) i) :=
    ⟨Nat.ne_of_gt hpos⟩
  exact (ZMod.finEquiv (masterCRTOptionFactor (w := w) (e := e) (V := V) i)).symm.toEquiv

noncomputable def masterCRTModulus_optionPiFinEquiv {w e V : ℕ} (he : 0 < e) :
    Fin (FromArithmetic.masterCRTModulus w e V) ≃
      (∀ i : Option (FromArithmetic.CRTPrimeRange w V),
        Fin (masterCRTOptionFactor (w := w) (e := e) (V := V) i)) := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  have hQ : 0 < Q := by dsimp [Q]; exact masterCRTModulus_pos
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  exact (ZMod.finEquiv Q).toEquiv.trans <|
    (masterCRTModulus_optionPiRingEquiv he).toEquiv.trans <|
      Equiv.piCongrRight fun i => crtOptionZModFinEquiv i

theorem masterCRTModulus_optionPiFinEquiv_some {w e V : ℕ} (he : 0 < e)
    (a : Fin (FromArithmetic.masterCRTModulus w e V))
    (p : FromArithmetic.CRTPrimeRange w V) :
    masterCRTModulus_optionPiFinEquiv he a (some p) =
      crtResidueProjection (w := w) (V := V)
        (Q := FromArithmetic.masterCRTModulus w e V) a p := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  have hQ : 0 < Q := by dsimp [Q]; exact masterCRTModulus_pos
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hcoord :
      (masterCRTModulus_optionPiRingEquiv he ((ZMod.finEquiv Q) a)) (some p) =
        (a.val : ZMod p.val) := by
    unfold masterCRTModulus_optionPiRingEquiv
    rw [RingEquiv.trans_apply]
    rw [ZMod.prodEquivPi_apply]
    rw [zmod_finEquiv_apply a]
    rw [map_natCast]
    have hdiv : p.val ∣
        ∏ i : Option (FromArithmetic.CRTPrimeRange w V),
          masterCRTOptionFactor (w := w) (e := e) (V := V) i :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ (some p))
    change (ZMod.cast (a.val : ZMod
      (∏ i : Option (FromArithmetic.CRTPrimeRange w V),
        masterCRTOptionFactor (w := w) (e := e) (V := V) i)) : ZMod p.val) =
      (a.val : ZMod p.val)
    exact ZMod.cast_natCast hdiv a.val
  apply Fin.ext
  change ((crtOptionZModFinEquiv (some p)
    ((masterCRTModulus_optionPiRingEquiv he) ((ZMod.finEquiv Q) a) (some p))).val) =
      a.val % p.val
  rw [hcoord]
  have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hpos : 0 < p.val := hp.pos
  letI : NeZero p.val := ⟨Nat.ne_of_gt hpos⟩
  have hfin : crtOptionZModFinEquiv (some p) (a.val : ZMod p.val) =
      (⟨a.val % p.val, by
        simpa [masterCRTOptionFactor] using Nat.mod_lt a.val hpos⟩ :
          Fin (masterCRTOptionFactor (w := w) (e := e) (V := V) (some p))) := by
    change (ZMod.finEquiv p.val).symm.toEquiv (a.val : ZMod p.val) = _
    have hcast : (ZMod.finEquiv p.val)
        (⟨a.val % p.val, Nat.mod_lt _ hpos⟩ : Fin p.val) =
        (a.val : ZMod p.val) := by
      rw [zmod_finEquiv_apply ⟨a.val % p.val, Nat.mod_lt _ hpos⟩]
      apply ZMod.val_injective p.val
      simp [ZMod.val_natCast, Nat.mod_mod]
    have hval : ((ZMod.finEquiv p.val).symm.toEquiv (a.val : ZMod p.val)).val =
        a.val % p.val := by
      have h := congrArg (fun z : ZMod p.val =>
        ((ZMod.finEquiv p.val).symm.toEquiv z).val) hcast
      simpa using h.symm
    apply Fin.ext
    simpa [crtOptionZModFinEquiv, masterCRTOptionFactor] using hval
  simpa [crtOptionZModFinEquiv, masterCRTOptionFactor] using congrArg Fin.val hfin

theorem masterCRTModulus_optionPiFinEquiv_none {w e V : ℕ} (he : 0 < e)
    (a : Fin (FromArithmetic.masterCRTModulus w e V)) :
    (masterCRTModulus_optionPiFinEquiv he a none).val =
      a.val % (primorial w ^ e) := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let B := primorial w ^ e
  have hQ : 0 < Q := by dsimp [Q]; exact masterCRTModulus_pos
  have hB : 0 < B := by dsimp [B]; exact pow_pos (primorial_pos w) e
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  letI : NeZero B := ⟨Nat.ne_of_gt hB⟩
  have hcoord :
      (masterCRTModulus_optionPiRingEquiv he ((ZMod.finEquiv Q) a)) none =
        (a.val : ZMod B) := by
    unfold masterCRTModulus_optionPiRingEquiv
    rw [RingEquiv.trans_apply]
    rw [ZMod.prodEquivPi_apply]
    rw [zmod_finEquiv_apply a]
    rw [map_natCast]
    have hdiv : B ∣
        ∏ i : Option (FromArithmetic.CRTPrimeRange w V),
          masterCRTOptionFactor (w := w) (e := e) (V := V) i :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ none)
    change (ZMod.cast (a.val : ZMod
      (∏ i : Option (FromArithmetic.CRTPrimeRange w V),
        masterCRTOptionFactor (w := w) (e := e) (V := V) i)) : ZMod B) =
      (a.val : ZMod B)
    exact ZMod.cast_natCast hdiv a.val
  change (crtOptionZModFinEquiv none
    ((masterCRTModulus_optionPiRingEquiv he) ((ZMod.finEquiv Q) a) none)).val =
      a.val % B
  rw [hcoord]
  have hfin : crtOptionZModFinEquiv none (a.val : ZMod B) =
      (⟨a.val % B, by simpa [masterCRTOptionFactor] using Nat.mod_lt a.val hB⟩ :
        Fin (masterCRTOptionFactor (w := w) (e := e) (V := V) none)) := by
    change (ZMod.finEquiv B).symm.toEquiv (a.val : ZMod B) = _
    have hcast : (ZMod.finEquiv B)
        (⟨a.val % B, Nat.mod_lt _ hB⟩ : Fin B) = (a.val : ZMod B) := by
      rw [zmod_finEquiv_apply ⟨a.val % B, Nat.mod_lt _ hB⟩]
      apply ZMod.val_injective B
      simp [ZMod.val_natCast, Nat.mod_mod]
    have hval : ((ZMod.finEquiv B).symm.toEquiv (a.val : ZMod B)).val = a.val % B := by
      have h := congrArg (fun z : ZMod B => ((ZMod.finEquiv B).symm.toEquiv z).val) hcast
      simpa using h.symm
    apply Fin.ext
    simpa [crtOptionZModFinEquiv, masterCRTOptionFactor] using hval
  simpa [crtOptionZModFinEquiv, masterCRTOptionFactor] using congrArg Fin.val hfin

noncomputable def masterCRTModulus_finCRTEquiv {w e V : ℕ} (he : 0 < e) :
    Fin (FromArithmetic.masterCRTModulus w e V) ≃
      Fin (primorial w ^ e) ×
        (∀ p : FromArithmetic.CRTPrimeRange w V, Fin p.val) := by
  simpa [masterCRTOptionFactor] using
    (masterCRTModulus_optionPiFinEquiv he).trans Equiv.piOptionEquivProd

theorem natCoprime_masterCRTModulus_factorization {w e V x : ℕ} :
    Nat.Coprime x (FromArithmetic.masterCRTModulus w e V) ↔
      Nat.Coprime x (primorial w ^ e) ∧
        ∀ p : FromArithmetic.CRTPrimeRange w V,
          Nat.Coprime (x % p.val) p.val := by
  rw [masterCRTModulus_eq_optionFactorProduct, Nat.coprime_fintype_prod_right_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [masterCRTOptionFactor] using h none
    · intro p
      have hp := h (some p)
      exact (ZMod.coprime_mod_iff_coprime x p.val).mpr
        (by simpa [masterCRTOptionFactor] using hp)
  · rintro ⟨hbase, hprime⟩ i
    cases i with
    | none => simpa [masterCRTOptionFactor] using hbase
    | some p =>
      exact (ZMod.coprime_mod_iff_coprime x p.val).mp (hprime p)

theorem masterCRTModulus_coprime_iff_projection {w e V : ℕ}
    (a : Fin (FromArithmetic.masterCRTModulus w e V)) :
    Nat.Coprime a.val (FromArithmetic.masterCRTModulus w e V) ↔
      Nat.Coprime a.val (primorial w ^ e) ∧
        ∀ p : FromArithmetic.CRTPrimeRange w V,
          Nat.Coprime (crtResidueProjection (w := w) (V := V)
            (Q := FromArithmetic.masterCRTModulus w e V) a p).val p.val := by
  simpa [crtResidueProjection] using
    (natCoprime_masterCRTModulus_factorization (w := w) (e := e) (V := V)
      (x := a.val))

theorem masterCRTModulus_coprime_iff_finCRTEquiv {w e V : ℕ} (he : 0 < e)
    (a : Fin (FromArithmetic.masterCRTModulus w e V)) :
    Nat.Coprime a.val (FromArithmetic.masterCRTModulus w e V) ↔
      Nat.Coprime (masterCRTModulus_finCRTEquiv he a).1.val (primorial w ^ e) ∧
        ∀ p : FromArithmetic.CRTPrimeRange w V,
          Nat.Coprime ((masterCRTModulus_finCRTEquiv he a).2 p).val p.val := by
  rw [masterCRTModulus_coprime_iff_projection (w := w) (e := e) (V := V) a]
  have hbase :
      (masterCRTModulus_finCRTEquiv he a).1.val = a.val % (primorial w ^ e) := by
    change (masterCRTModulus_optionPiFinEquiv he a none).val = _
    exact masterCRTModulus_optionPiFinEquiv_none he a
  have hprime (p : FromArithmetic.CRTPrimeRange w V) :
      (masterCRTModulus_finCRTEquiv he a).2 p =
        crtResidueProjection (w := w) (V := V)
          (Q := FromArithmetic.masterCRTModulus w e V) a p := by
    change masterCRTModulus_optionPiFinEquiv he a (some p) = _
    exact masterCRTModulus_optionPiFinEquiv_some he a p
  constructor
  · rintro ⟨hbase', hprime'⟩
    refine ⟨?_, ?_⟩
    · rw [hbase]
      exact (ZMod.coprime_mod_iff_coprime a.val (primorial w ^ e)).mpr hbase'
    · intro p
      rw [hprime p]
      exact hprime' p
  · rintro ⟨hbase', hprime'⟩
    refine ⟨?_, ?_⟩
    · have hc : Nat.Coprime (a.val % (primorial w ^ e)) (primorial w ^ e) := by
        simpa [hbase] using hbase'
      exact (ZMod.coprime_mod_iff_coprime a.val (primorial w ^ e)).mp hc
    · intro p
      rw [← hprime p]
      exact hprime' p

noncomputable def unitsEquivIsUnitSubtype {M : Type*} [Monoid M] :
    Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext (by simp)
  right_inv x := Subtype.ext x.2.unit_spec

theorem sum_isUnit_eq_card_units {M : Type*} [Monoid M] [Fintype M]
    [Fintype Mˣ] [DecidablePred (fun x : M => IsUnit x)] :
    (∑ x : M, if IsUnit x then (1 : ℝ) else 0) = (Fintype.card Mˣ : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : M => IsUnit x), (1 : ℝ) := by
      rw [← Finset.sum_filter]
    _ = ((Finset.univ.filter (fun x : M => IsUnit x)).card : ℝ) := by
      simp
    _ = (Fintype.card {x : M // IsUnit x} : ℝ) := by
      exact_mod_cast (Fintype.card_subtype (fun x : M => IsUnit x)).symm
    _ = _ := by
      exact_mod_cast (Fintype.card_congr
        (unitsEquivIsUnitSubtype (M := M)).symm)

theorem sum_coprime_fin_eq_totient {n : ℕ} (hn : 0 < n) :
    (∑ a : Fin n, if Nat.Coprime a.val n then (1 : ℝ) else 0) =
      (Nat.totient n : ℝ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : Finite (ZMod n)ˣ :=
    Finite.of_injective (fun u : (ZMod n)ˣ => (u : ZMod n)) Units.val_injective
  letI : Fintype (ZMod n)ˣ := Fintype.ofFinite (ZMod n)ˣ
  calc
    _ = ∑ z : ZMod n, if IsUnit z then (1 : ℝ) else 0 := by
      apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
      intro a
      change (if Nat.Coprime a.val n then (1 : ℝ) else 0) =
        if IsUnit ((ZMod.finEquiv n) a) then 1 else 0
      rw [zmod_finEquiv_apply a]
      simp [ZMod.isUnit_iff_coprime]
    _ = (Fintype.card (ZMod n)ˣ : ℝ) := sum_isUnit_eq_card_units
    _ = _ := by rw [ZMod.card_units_eq_totient n]

theorem uniformUnitResidueLaw_sum_one {Q : ℕ} (hQ : 0 < Q) :
    (∑ a : Fin Q, uniformUnitResidueLaw Q a) = 1 := by
  classical
  have hφ : 0 < (Nat.totient Q : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hQ)
  have hterm (a : Fin Q) : uniformUnitResidueLaw Q a =
      (if Nat.Coprime a.val Q then (1 : ℝ) else 0) / (Nat.totient Q : ℝ) := by
    unfold uniformUnitResidueLaw
    by_cases h : Nat.Coprime a.val Q
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  calc
    _ = (∑ a : Fin Q, if Nat.Coprime a.val Q then (1 : ℝ) else 0) /
        (Nat.totient Q : ℝ) := by
      rw [Finset.sum_congr rfl (fun a ha => hterm a), Finset.sum_div]
    _ = (Nat.totient Q : ℝ) / (Nat.totient Q : ℝ) := by
      rw [sum_coprime_fin_eq_totient hQ]
    _ = 1 := div_self (ne_of_gt hφ)

theorem masterCRTModulus_totient {w e V : ℕ} (he : 0 < e) :
    Nat.totient (FromArithmetic.masterCRTModulus w e V) =
      Nat.totient (primorial w ^ e) *
        ∏ p : FromArithmetic.CRTPrimeRange w V, (p.val - 1) := by
  rw [masterCRTModulus_eq_base_mul_crtPrimeProduct,
    Nat.totient_mul (primorialPow_coprime_crtPrimeProduct he),
    crtPrimeProduct_totient]

theorem finiteSum_mul_singletonIndicator {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℝ) :
    (∑ x, f x * (if x = a then 1 else 0)) = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro x hx hxa
    simp [hxa]
  · simp

theorem pkgElim_sum_ne_subtype_eq_filter {α : Type*} [Fintype α] [DecidableEq α]
    (I : α) (f : {x : α // x ≠ I} → ℝ) :
    (∑ x : α, if h : x ≠ I then f ⟨x, h⟩ else 0) =
      ∑ x : {x : α // x ≠ I}, f x := by
  classical
  let pred : α → Prop := fun x => x ≠ I
  let g : α → ℝ := fun x => if h : pred x then f ⟨x, h⟩ else 0
  have hS : (Finset.univ : Finset {x : α // pred x}) =
      (Finset.univ : Finset α).subtype pred := by
    ext x
    simp [pred]
  change (∑ x : α, g x) = ∑ x : {x : α // pred x}, f x
  calc
    _ = ∑ x ∈ (Finset.univ : Finset α).filter pred, g x := by
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : pred x <;> simp [g, pred, h]
    _ = ∑ x : {x : α // pred x}, f x := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      rw [hS]
      apply Finset.sum_congr rfl
      intro x hx
      simp [g, pred, x.property]

theorem uniformUnitResidueLaw_crtProjection {w e V : ℕ} (he : 0 < e)
    (r : FromArithmetic.CRTResidues w V) :
    (∑ a : Fin (FromArithmetic.masterCRTModulus w e V),
      uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V) a *
        (if crtResidueProjection (w := w) (V := V)
          (Q := FromArithmetic.masterCRTModulus w e V) a = r then 1 else 0)) =
      ∏ p : FromArithmetic.CRTPrimeRange w V,
        if Nat.Coprime (r p).val p.val then
          1 / ((p.val - 1 : ℕ) : ℝ) else 0 := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let B := primorial w ^ e
  let P := ∀ p : FromArithmetic.CRTPrimeRange w V, Fin p.val
  let E : Fin Q ≃ Fin B × P := masterCRTModulus_finCRTEquiv he
  let c : ℝ := 1 / (Nat.totient Q : ℝ)
  have hB : 0 < B := by dsimp [B]; exact pow_pos (primorial_pos w) e
  have hTot : (Nat.totient Q : ℝ) =
      (Nat.totient B : ℝ) * ∏ p : FromArithmetic.CRTPrimeRange w V,
        ((p.val - 1 : ℕ) : ℝ) := by
    dsimp [Q, B]
    exact_mod_cast masterCRTModulus_totient he
  have hBtot : 0 < (Nat.totient B : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hB)
  have hFactor (p : FromArithmetic.CRTPrimeRange w V) :
      0 < ((p.val - 1 : ℕ) : ℝ) := by
    have hp : p.val.Prime := (Finset.mem_filter.mp p.property).2
    have hp' : 1 < p.val := hp.one_lt
    exact_mod_cast (Nat.sub_pos_of_lt hp')
  have hPpos : 0 < ∏ p : FromArithmetic.CRTPrimeRange w V,
      ((p.val - 1 : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact hFactor p
  let primeFinset : Finset ℕ := (Finset.Ioc w (V + 1)).filter Nat.Prime
  have hattach : primeFinset.attach =
      ((Finset.Ioc w (V + 1)).filter Nat.Prime).attach := by
    rfl
  have hprodAttach :
      (∏ p : FromArithmetic.CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ)) =
        ∏ p ∈ primeFinset.attach, ((p.1 - 1 : ℕ) : ℝ) := by
    rfl
  have hratio : c * (Nat.totient B : ℝ) =
      1 / ∏ p : FromArithmetic.CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ) := by
    dsimp [c]
    rw [hTot]
    field_simp [ne_of_gt hBtot, ne_of_gt hPpos]
    rw [hprodAttach]
    rw [hattach]
    have hPpos' : 0 <
        ∏ x ∈ ((Finset.Ioc w (V + 1)).filter Nat.Prime).attach,
          ((x.1 - 1 : ℕ) : ℝ) := by
      simpa [hprodAttach, hattach] using hPpos
    exact (mul_inv_cancel₀ (ne_of_gt hPpos')).symm
  have hprodInv :
      (∏ p : FromArithmetic.CRTPrimeRange w V,
        1 / ((p.val - 1 : ℕ) : ℝ)) =
        1 / ∏ p : FromArithmetic.CRTPrimeRange w V, ((p.val - 1 : ℕ) : ℝ) := by
    calc
      _ = ∏ p : FromArithmetic.CRTPrimeRange w V,
          (((p.val - 1 : ℕ) : ℝ)⁻¹) := by simp [one_div]
      _ = (∏ p : FromArithmetic.CRTPrimeRange w V,
          ((p.val - 1 : ℕ) : ℝ))⁻¹ := by rw [Finset.prod_inv_distrib]
      _ = _ := by simp [one_div]
  have hsnd (a : Fin Q) : (E a).2 =
      fun p => crtResidueProjection (w := w) (V := V) (Q := Q) a p := by
    funext p
    change masterCRTModulus_optionPiFinEquiv he a (some p) = _
    exact masterCRTModulus_optionPiFinEquiv_some he a p
  let g : Fin B × P → ℝ := fun x =>
    (if Nat.Coprime x.1.val B ∧ ∀ p, Nat.Coprime (x.2 p).val p.val then c else 0) *
      (if x.2 = r then 1 else 0)
  have hterm (a : Fin Q) :
      uniformUnitResidueLaw Q a *
        (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0) =
        g (E a) := by
    have hunit := masterCRTModulus_coprime_iff_finCRTEquiv he a
    have hdelta :
        (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then (1 : ℝ) else 0) =
          (if (E a).2 = r then (1 : ℝ) else 0) := by
      rw [hsnd a]
    by_cases ha : Nat.Coprime a.val Q
    · have hc := hunit.mp ha
      calc
        _ = uniformUnitResidueLaw Q a * (if (E a).2 = r then 1 else 0) := by
          exact congrArg (fun x : ℝ => uniformUnitResidueLaw Q a * x) hdelta
        _ = g (E a) := by
          unfold uniformUnitResidueLaw g
          rw [if_pos ha, if_pos hc]
    · have hc : ¬ (Nat.Coprime (E a).1.val B ∧
          ∀ p, Nat.Coprime ((E a).2 p).val p.val) := by
        intro h
        exact ha (hunit.mpr h)
      calc
        _ = uniformUnitResidueLaw Q a * (if (E a).2 = r then 1 else 0) := by
          exact congrArg (fun x : ℝ => uniformUnitResidueLaw Q a * x) hdelta
        _ = g (E a) := by
          unfold uniformUnitResidueLaw g
          rw [if_neg ha, if_neg hc]
      
  have hsum :
      (∑ a : Fin Q,
        uniformUnitResidueLaw Q a *
          (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)) =
      ∑ x : Fin B × P, g x := by
    calc
      _ = ∑ a : Fin Q, g (E a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a
      _ = ∑ x : Fin B × P, g x := by
        exact Fintype.sum_equiv E (fun a => g (E a)) g (fun _ => rfl)
  have hcollapse (b : Fin B) :
      (∑ y : P, g (b, y)) =
        if Nat.Coprime b.val B ∧ ∀ p, Nat.Coprime (r p).val p.val then c else 0 := by
    have h := finiteSum_mul_singletonIndicator (α := P) r
      (fun y => if Nat.Coprime b.val B ∧ ∀ p, Nat.Coprime (y p).val p.val then c else 0)
    simpa [g] using h
  have heval :
      (∑ x : Fin B × P, g x) =
        ∑ b : Fin B,
          if Nat.Coprime b.val B ∧ ∀ p, Nat.Coprime (r p).val p.val then c else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b hb
    exact hcollapse b
  by_cases hr : ∀ p : FromArithmetic.CRTPrimeRange w V,
      Nat.Coprime (r p).val p.val
  · have hscale :
        (∑ b : Fin B, if Nat.Coprime b.val B ∧ (∀ p, Nat.Coprime (r p).val p.val)
          then c else 0) = c * ∑ b : Fin B, if Nat.Coprime b.val B then 1 else 0 := by
      calc
        _ = ∑ b : Fin B, (if Nat.Coprime b.val B then 1 else 0) * c := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hb' : Nat.Coprime b.val B
          · have hcond : Nat.Coprime b.val B ∧
                (∀ p, Nat.Coprime (r p).val p.val) := ⟨hb', hr⟩
            calc
              _ = c := if_pos hcond
              _ = (if Nat.Coprime b.val B then 1 else 0) * c := by simp [hb']
          · have hcond : ¬ (Nat.Coprime b.val B ∧
                (∀ p, Nat.Coprime (r p).val p.val)) := by
              rintro ⟨hu, _⟩
              exact hb' hu
            calc
              _ = 0 := if_neg hcond
              _ = (if Nat.Coprime b.val B then 1 else 0) * c := by simp [hb']
        _ = (∑ b : Fin B, if Nat.Coprime b.val B then 1 else 0) * c := by
          rw [← Finset.sum_mul]
        _ = c * ∑ b : Fin B, if Nat.Coprime b.val B then 1 else 0 := by ring
    calc
      _ = ∑ b : Fin B,
          if Nat.Coprime b.val B ∧ (∀ p, Nat.Coprime (r p).val p.val) then c else 0 :=
        hsum.trans heval
      _ = c * (Nat.totient B : ℝ) := by
        rw [hscale, sum_coprime_fin_eq_totient hB]
      _ = 1 / ∏ p : FromArithmetic.CRTPrimeRange w V,
          ((p.val - 1 : ℕ) : ℝ) := hratio
      _ = ∏ p : FromArithmetic.CRTPrimeRange w V,
          1 / ((p.val - 1 : ℕ) : ℝ) := hprodInv.symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [hr p]
  · obtain ⟨p, hp⟩ := not_forall.mp hr
    have hleft :
        (∑ b : Fin B,
          if Nat.Coprime b.val B ∧ (∀ p, Nat.Coprime (r p).val p.val) then c else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hfalse : ¬ (Nat.Coprime b.val B ∧
          ∀ p, Nat.Coprime (r p).val p.val) := by
        rintro ⟨_, hall⟩
        exact hr hall
      exact if_neg hfalse
    have hright :
        (∏ p : FromArithmetic.CRTPrimeRange w V,
          if Nat.Coprime (r p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simp [hp]
    calc
      _ = ∑ b : Fin B,
          if Nat.Coprime b.val B ∧ (∀ p, Nat.Coprime (r p).val p.val) then c else 0 :=
        hsum.trans heval
      _ = 0 := hleft
      _ = _ := hright.symm

theorem primeTupleCRTLaw_eq_prod_marginals {m w V : ℕ}
    (lo hi : Fin m → ℕ) (r : Fin m → FromArithmetic.CRTResidues w V) :
    FromArithmetic.primeTupleCRTLaw lo hi w V r =
      ∏ i, ∑' p : ℕ,
        primePoolLaw (lo i) (hi i) p *
          (if FromArithmetic.integerCRTResidues w V p = r i then 1 else 0) := by
  classical
  let I : Fin m → Finset ℕ := fun i => (Finset.Ico (lo i) (hi i)).filter Nat.Prime
  let f : Fin m → ℕ → ℝ := fun i p => primePoolLaw (lo i) (hi i) p *
    (if FromArithmetic.integerCRTResidues w V p = r i then 1 else 0)
  have hsupp (i : Fin m) (p : ℕ) (hp : p ∉ I i) : f i p = 0 := by
    have hcond : ¬ (lo i ≤ p ∧ p < hi i ∧ Nat.Prime p) := by
      intro h
      exact hp (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    unfold f primePoolLaw
    simp [hcond]
  have hterm (p : Fin m → ℕ) :
      independentPrimePoolMass lo hi p *
        (if (fun i => FromArithmetic.integerCRTResidues w V (p i)) = r then 1 else 0) =
          ∏ i, f i (p i) := by
    unfold independentPrimePoolMass
    rw [function_eq_indicator_prod (ι := Fin m)
      (α := FromArithmetic.CRTResidues w V)
      (fun i => FromArithmetic.integerCRTResidues w V (p i)) r]
    rw [← Finset.prod_mul_distrib]
  unfold FromArithmetic.primeTupleCRTLaw
  calc
    (∑' p : Fin m → ℕ,
        independentPrimePoolMass lo hi p *
          (if (fun i => FromArithmetic.integerCRTResidues w V (p i)) = r then 1 else 0)) =
        ∑' p : Fin m → ℕ, ∏ i, f i (p i) := by
      apply tsum_congr
      intro p
      exact hterm p
    _ = ∏ i, ∑ p ∈ I i, f i p :=
      product_tsum_eq_product_sum_of_finite_support f I hsupp
    _ = ∏ i, ∑' p : ℕ, f i p := by
      apply Finset.prod_congr rfl
      intro i hi
      symm
      rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (f := f i) (s := I i)
        (hsupp i)]

theorem primePoolLaw_crtProjection {w V Q lo hi : ℕ}
    (hQ : 0 < Q)
    (hdiv : ∀ p : FromArithmetic.CRTPrimeRange w V, p.val ∣ Q)
    (hmass : 0 < primePoolMass lo hi) (r : FromArithmetic.CRTResidues w V) :
    ∑' n : ℕ, primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0) =
      ∑ a : Fin Q, primePoolResidueLaw lo hi Q a *
        (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0) := by
  classical
  let S : Finset ℕ := (Finset.Ico lo hi).filter Nat.Prime
  have hsupp : ∀ n ∉ S,
      primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0) = 0 := by
    intro n hn
    have hcond : ¬ (lo ≤ n ∧ n < hi ∧ Nat.Prime n) := by
      intro h
      exact hn (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    simp [primePoolLaw, hcond]
  have hinner (n : ℕ) :
      ∑ a : Fin Q,
        (if n % Q = a.val then 1 / (n : ℝ) else 0) *
          (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0) =
        (1 / (n : ℝ)) *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0) := by
    let a₀ : Fin Q := ⟨n % Q, Nat.mod_lt _ hQ⟩
    have hproj := crtResidueProjection_mod hQ hdiv n
    have htest (a : Fin Q) :
        (if n % Q = a.val then 1 / (n : ℝ) else 0) =
          (if a = a₀ then 1 / (n : ℝ) else 0) := by
      by_cases ha : a = a₀
      · subst a
        simp [a₀]
      · have hneq : n % Q ≠ a.val := by
          intro hval
          apply ha
          apply Fin.ext
          simpa [a₀] using hval.symm
        simp [ha, hneq]
    have hterm (a : Fin Q) :
        (if n % Q = a.val then 1 / (n : ℝ) else 0) *
          (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0) =
        if a = a₀ then
          (1 / (n : ℝ)) *
            (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)
        else 0 := by
      rw [htest a]
      by_cases ha : a = a₀ <;> simp [ha]
    calc
      _ = ∑ a : Fin Q, if a = a₀ then
          (1 / (n : ℝ)) *
            (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)
        else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a
      _ = (1 / (n : ℝ)) *
          (if crtResidueProjection (w := w) (V := V) (Q := Q) a₀ = r then 1 else 0) := by
        simp [Finset.sum_ite_eq']
      _ = _ := by simp [a₀, hproj]
  have hLeft :
      (∑' n : ℕ, primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) =
      (∑ n ∈ S, 1 / (n : ℝ) *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) /
        primePoolMass lo hi := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := fun n => primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0))
      (s := S) hsupp]
    calc
      (∑ n ∈ S, primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) =
        ∑ n ∈ S, (1 / (n : ℝ)) / primePoolMass lo hi *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' : lo ≤ n ∧ n < hi ∧ Nat.Prime n := by
          rcases Finset.mem_filter.mp hn with ⟨hIco, hp⟩
          exact ⟨(Finset.mem_Ico.mp hIco).1, (Finset.mem_Ico.mp hIco).2, hp⟩
        simp [primePoolLaw, hn']
      _ = (∑ n ∈ S, 1 / (n : ℝ) *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) /
            primePoolMass lo hi := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hRight :
      (∑ a : Fin Q, primePoolResidueLaw lo hi Q a *
        (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)) =
      (∑ n ∈ S, 1 / (n : ℝ) *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) /
        primePoolMass lo hi := by
    unfold primePoolResidueLaw
    calc
      _ = (∑ a : Fin Q,
          (∑ n ∈ S, (if n % Q = a.val then 1 / (n : ℝ) else 0) *
            (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0))) /
            primePoolMass lo hi := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_mul]
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply congrArg (fun x => x / primePoolMass lo hi)
        apply Finset.sum_congr rfl
        intro n hn
        exact hinner n
  exact hLeft.trans hRight.symm

theorem primePoolCRTLaw_projection_tv {w V Q lo hi : ℕ}
    (hQ : 0 < Q)
    (hdiv : ∀ p : FromArithmetic.CRTPrimeRange w V, p.val ∣ Q)
    (hmass : 0 < primePoolMass lo hi) :
    finiteL1
      (fun r : FromArithmetic.CRTResidues w V =>
        ∑' n : ℕ, primePoolLaw lo hi n *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0))
      (fun r => ∑ a : Fin Q,
        uniformUnitResidueLaw Q a *
          (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)) ≤
      finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
  classical
  let f : Fin Q → FromArithmetic.CRTResidues w V :=
    crtResidueProjection (w := w) (V := V) (Q := Q)
  have hactual :
      (fun r : FromArithmetic.CRTResidues w V =>
        ∑' n : ℕ, primePoolLaw lo hi n *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) =
        finitePushforward f (primePoolResidueLaw lo hi Q) := by
    funext r
    simpa [finitePushforward, f] using
      primePoolLaw_crtProjection hQ hdiv hmass r
  have huniformPush : finitePushforward f (uniformUnitResidueLaw Q) =
      fun r => ∑ a : Fin Q, uniformUnitResidueLaw Q a *
        (if f a = r then 1 else 0) := by
    funext r
    unfold finitePushforward
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : f a = r <;> simp [h]
  have hUniform :
      (fun r => ∑ a : Fin Q, uniformUnitResidueLaw Q a *
        (if crtResidueProjection (w := w) (V := V) (Q := Q) a = r then 1 else 0)) =
        finitePushforward f (uniformUnitResidueLaw Q) := by
    simpa [f] using huniformPush.symm
  rw [hactual, hUniform]
  exact finiteL1_pushforward_le f (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q)

theorem primePoolCRTLaw_probability {w V Q lo hi : ℕ}
    (hQ : 0 < Q) (hdiv : ∀ p : FromArithmetic.CRTPrimeRange w V, p.val ∣ Q)
    (hmass : 0 < primePoolMass lo hi) :
    (∀ r : FromArithmetic.CRTResidues w V,
      0 ≤ ∑' n : ℕ, primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) ∧
    (∑ r : FromArithmetic.CRTResidues w V,
      ∑' n : ℕ, primePoolLaw lo hi n *
        (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) = 1 := by
  classical
  let f : Fin Q → FromArithmetic.CRTResidues w V :=
    crtResidueProjection (w := w) (V := V) (Q := Q)
  have hactual :
      (fun r : FromArithmetic.CRTResidues w V =>
        ∑' n : ℕ, primePoolLaw lo hi n *
          (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)) =
        finitePushforward f (primePoolResidueLaw lo hi Q) := by
    funext r
    simpa [finitePushforward, f] using primePoolLaw_crtProjection hQ hdiv hmass r
  constructor
  · intro r
    apply tsum_nonneg
    intro n
    have hμ := pkgElim_primePoolLaw_nonneg hmass n
    split_ifs <;> positivity
  · calc
      _ = ∑ r : FromArithmetic.CRTResidues w V,
          finitePushforward f (primePoolResidueLaw lo hi Q) r := by rw [hactual]
      _ = ∑ a : Fin Q, primePoolResidueLaw lo hi Q a := finitePushforward_sum f _
      _ = 1 := primePoolResidueLaw_sum_one hQ hmass

theorem primeTupleCRTLaw_finiteL1_le {s w e V lo hi : ℕ}
    (he : 0 < e) (hmass : 0 < primePoolMass lo hi) :
    finiteL1
      (FromArithmetic.primeTupleCRTLaw
        (fun _ : Fin s => lo) (fun _ => hi) w V)
      (FromArithmetic.uniformPrimeTupleCRTLaw w V) ≤
      (s : ℝ) * finiteL1
        (primePoolResidueLaw lo hi (FromArithmetic.masterCRTModulus w e V))
        (uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V)) := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let f : Fin Q → FromArithmetic.CRTResidues w V :=
    crtResidueProjection (w := w) (V := V) (Q := Q)
  let μ₀ : FromArithmetic.CRTResidues w V → ℝ := fun r =>
    ∑' n : ℕ, primePoolLaw lo hi n *
      (if FromArithmetic.integerCRTResidues w V n = r then 1 else 0)
  let ν₀ : FromArithmetic.CRTResidues w V → ℝ := fun r =>
    finitePushforward f (uniformUnitResidueLaw Q) r
  let μ : Fin s → FromArithmetic.CRTResidues w V → ℝ := fun _ => μ₀
  let ν : Fin s → FromArithmetic.CRTResidues w V → ℝ := fun _ => ν₀
  have hQ : 0 < Q := by dsimp [Q]; exact masterCRTModulus_pos
  have hdiv : ∀ p : FromArithmetic.CRTPrimeRange w V, p.val ∣ Q := by
    intro p
    rcases Finset.mem_filter.mp p.property with ⟨hIoc, hp⟩
    rcases Finset.mem_Ioc.mp hIoc with ⟨hwp, hpV⟩
    exact masterCRTModulus_mediumPrime_dvd hp hwp hpV
  have hprob := primePoolCRTLaw_probability hQ hdiv hmass
  have hμnonneg : ∀ i r, 0 ≤ μ i r := by
    intro i r
    exact hprob.1 r
  have hμnorm : ∀ i, ∑ r, μ i r = 1 := by
    intro i
    exact hprob.2
  have hνnonneg : ∀ i r, 0 ≤ ν i r := by
    intro i r
    exact finitePushforward_nonneg f (uniformUnitResidueLaw Q)
      (uniformUnitResidueLaw_nonneg hQ) r
  have hνnorm : ∀ i, ∑ r, ν i r = 1 := by
    intro i
    calc
      _ = ∑ r, finitePushforward f (uniformUnitResidueLaw Q) r := rfl
      _ = ∑ a : Fin Q, uniformUnitResidueLaw Q a := finitePushforward_sum f _
      _ = 1 := uniformUnitResidueLaw_sum_one hQ
  have hνdirect : ν₀ = fun r =>
      ∑ a : Fin Q, uniformUnitResidueLaw Q a * (if f a = r then 1 else 0) := by
    funext r
    unfold ν₀ finitePushforward
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : f a = r <;> simp [h]
  have hTVone : finiteL1 μ₀ ν₀ ≤
      finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
    have h := primePoolCRTLaw_projection_tv hQ hdiv hmass
    simpa [μ₀, ν₀, f, hνdirect] using h
  have hActual (r : Fin s → FromArithmetic.CRTResidues w V) :
      FromArithmetic.primeTupleCRTLaw (fun _ : Fin s => lo) (fun _ => hi) w V r =
        ∏ i, μ i (r i) := by
    simpa [μ, μ₀] using
      (primeTupleCRTLaw_eq_prod_marginals
        (fun _ : Fin s => lo) (fun _ => hi) r)
  have hNuProd (r : FromArithmetic.CRTResidues w V) :
      ν₀ r = ∏ p : FromArithmetic.CRTPrimeRange w V,
        if Nat.Coprime (r p).val p.val then 1 / ((p.val - 1 : ℕ) : ℝ) else 0 := by
    unfold ν₀ finitePushforward
    have hsumEq :
        (∑ a : Fin Q, if f a = r then uniformUnitResidueLaw Q a else 0) =
          (∑ a : Fin Q, uniformUnitResidueLaw Q a * (if f a = r then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : f a = r <;> simp [h]
    rw [hsumEq]
    exact uniformUnitResidueLaw_crtProjection (w := w) (e := e) (V := V) he r
  have hUniform (r : Fin s → FromArithmetic.CRTResidues w V) :
      FromArithmetic.uniformPrimeTupleCRTLaw w V r = ∏ i, ν i (r i) := by
    unfold FromArithmetic.uniformPrimeTupleCRTLaw
    apply Finset.prod_congr rfl
    intro i hi
    exact (hNuProd (r i)).symm
  have hProduct := finiteL1_product_probability_le
    (μ := μ) (ν := ν) hμnonneg hνnonneg hμnorm hνnorm
  have hCoordTV : ∀ i : Fin s,
      finiteL1 (μ i) (ν i) ≤
        finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
    intro i
    exact hTVone
  calc
    _ = finiteL1 (fun x : Fin s → FromArithmetic.CRTResidues w V => ∏ i, μ i (x i))
        (fun x => ∏ i, ν i (x i)) := by
      rw [funext hActual, funext hUniform]
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) := hProduct
    _ ≤ ∑ i : Fin s,
          finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hCoordTV i
    _ = (s : ℝ) * finiteL1
          (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by simp

theorem pkgElim_independentPrimePoolMass_tsum_one {m : ℕ} (lo hi : Fin m → ℕ)
    (hmass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p = 1 := by
  classical
  let I : Fin m → Finset ℕ := fun i => (Finset.Ico (lo i) (hi i)).filter Nat.Prime
  let S : Finset (Fin m → ℕ) := Fintype.piFinset I
  have hcoord (i : Fin m) : ∑ p ∈ I i, primePoolLaw (lo i) (hi i) p = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (f := primePoolLaw (lo i) (hi i)) (s := I i)]
    · exact pkgElim_primePoolLaw_tsum_one (hmass i)
    · intro p hp
      unfold primePoolLaw
      rw [if_neg]
      intro h
      exact hp (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
  have hsupp : ∀ p ∉ S, independentPrimePoolMass lo hi p = 0 := by
    intro p hp
    have hnotall : ∃ i, p i ∉ I i := by
      by_contra h
      push_neg at h
      apply hp
      simpa [S] using (show p ∈ Fintype.piFinset I from by simpa using h)
    obtain ⟨i, hnotI⟩ := hnotall
    have hz : primePoolLaw (lo i) (hi i) (p i) = 0 := by
      unfold primePoolLaw
      rw [if_neg]
      intro h
      exact hnotI (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    unfold independentPrimePoolMass
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  exact productLaw_tsum_one_of_finite_support
    (μ := fun i p => primePoolLaw (lo i) (hi i) p) (S := I)
    (fun i p hp => by
      unfold primePoolLaw
      rw [if_neg]
      intro h
      exact hp (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)) hcoord

theorem independentPrimePoolProbability_compl {m : ℕ} (lo hi : Fin m → ℕ)
    (hmass : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (E : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability lo hi E +
      independentPrimePoolProbability lo hi (fun p => ¬ E p) = 1 := by
  classical
  let I : Fin m → Finset ℕ := fun i => (Finset.Ico (lo i) (hi i)).filter Nat.Prime
  let S : Finset (Fin m → ℕ) := Fintype.piFinset I
  have hsupp : ∀ p ∉ S, independentPrimePoolMass lo hi p = 0 := by
    intro p hp
    have hnotall : ∃ i, p i ∉ I i := by
      by_contra h
      push_neg at h
      apply hp
      simpa [S] using (show p ∈ Fintype.piFinset I from by simpa using h)
    obtain ⟨i, hnotI⟩ := hnotall
    have hz : ¬ (lo i ≤ p i ∧ p i < hi i ∧ Nat.Prime (p i)) := by
      intro h
      exact hnotI (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    have hzi : primePoolLaw (lo i) (hi i) (p i) = 0 := by
      unfold primePoolLaw
      simp [hz]
    change (∏ j, primePoolLaw (lo j) (hi j) (p j)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzi
  have htotal := pkgElim_independentPrimePoolMass_tsum_one lo hi hmass
  have hsumE : independentPrimePoolProbability lo hi E =
      ∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then 1 else 0) := by
    unfold independentPrimePoolProbability
    rw [tsum_eq_sum (L := SummationFilter.unconditional (Fin m → ℕ))
      (f := fun p => independentPrimePoolMass lo hi p * (if E p then 1 else 0))
      (s := S) (by intro p hp; simp [hsupp p hp])]
  have hsumNotE : independentPrimePoolProbability lo hi (fun p => ¬ E p) =
      ∑ p ∈ S, independentPrimePoolMass lo hi p * (if ¬ E p then 1 else 0) := by
    unfold independentPrimePoolProbability
    simpa using (tsum_eq_sum (L := SummationFilter.unconditional (Fin m → ℕ))
      (f := fun p => independentPrimePoolMass lo hi p * (if ¬ E p then 1 else 0))
      (s := S) (by intro p hp; simp [hsupp p hp]))
  have hsumMass : (∑ p ∈ S, independentPrimePoolMass lo hi p) = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional (Fin m → ℕ))
      (f := independentPrimePoolMass lo hi) (s := S) (by intro p hp; simp [hsupp p hp])]
    exact htotal
  calc
    independentPrimePoolProbability lo hi E +
        independentPrimePoolProbability lo hi (fun p => ¬ E p) =
      ∑ p ∈ S, independentPrimePoolMass lo hi p := by
        rw [hsumE, hsumNotE, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h : E p <;> simp [h]
    _ = 1 := hsumMass

theorem gapSlotProbability_tendsto_one_of_bad {K s q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (l : Fin K)
    (E : ℕ → (Fin q → ℕ) → Prop)
    (hbad : Tendsto (fun N => gapSlotProbability S l N (fun p => ¬ E N p))
      atTop (𝓝 0)) :
    Tendsto (fun N => gapSlotProbability S l N (E N)) atTop (𝓝 1) := by
  classical
  have hratio : Tendsto
      (fun N => primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper /
        (masterScaleV S.core.parameters N l : ℝ)) atTop atTop :=
    by
      simpa [pow_one] using S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)
  have hmasspos : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper := by
    filter_upwards [hratio.eventually_ge_atTop (1 : ℝ)] with N hN
    have hV : 0 < (masterScaleV S.core.parameters N l : ℝ) := by
      unfold masterScaleV
      positivity
    have hmul : (masterScaleV S.core.parameters N l : ℝ) ≤
        primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper :=
      by simpa using (le_div_iff₀ hV).mp hN
    linarith
  have hEq : ∀ᶠ N in atTop,
      gapSlotProbability S l N (E N) +
        gapSlotProbability S l N (fun p => ¬ E N p) = 1 := by
    filter_upwards [hmasspos] with N hmass
    let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N l).lower
    let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N l).upper
    have h := independentPrimePoolProbability_compl lo hi (fun _ => hmass) (E N)
    simpa [gapSlotProbability, lo, hi] using h
  have hcongr : (fun N => gapSlotProbability S l N (E N)) =ᶠ[atTop]
      fun N => 1 - gapSlotProbability S l N (fun p => ¬ E N p) := by
    filter_upwards [hEq] with N hN
    linarith
  apply (tendsto_congr' hcongr).2
  simpa using (tendsto_const_nhds.sub hbad)

theorem harmonicProductLaw_eq_subtype_sum {k W : ℕ} (X : Fin k → ℕ)
    (σ : ℕ) :
    harmonicProductLaw W X σ =
      ∑ t : ∀ i : Fin k,
          {x : ℕ // x ∈ (Finset.Ico (X i) ((X i) ^ 2)).filter (fun x => Nat.Coprime x W)},
        (if (∏ i, (t i).val) = σ then 1 else 0) *
          ∏ i, harmonicNatLaw (X i) W (t i).val := by
  classical
  let I : Fin k → Finset ℕ := fun i =>
    (Finset.Ico (X i) ((X i) ^ 2)).filter fun x => Nat.Coprime x W
  let rawMap (t : ∀ i : Fin k, {x : ℕ // x ∈ I i}) : Fin k → ℕ :=
    fun i => (t i).val
  let s : Finset (Fin k → ℕ) := Finset.univ.image rawMap
  have hinj : Function.Injective rawMap := by
    intro t u h
    funext i
    exact Subtype.ext (congrFun h i)
  have hsupp : ∀ t ∉ s,
      (if (∏ i, t i) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (X i) W (t i) = 0 := by
    intro t ht
    have hnotall : ∃ i, t i ∉ I i := by
      by_contra h
      push_neg at h
      apply ht
      refine Finset.mem_image.mpr
        ⟨(fun i : Fin k => (⟨t i, h i⟩ : {x : ℕ // x ∈ I i})), Finset.mem_univ _, ?_⟩
      funext i
      rfl
    obtain ⟨i, hi⟩ := hnotall
    have hcond : ¬ (X i ≤ t i ∧ t i < (X i) ^ 2 ∧ Nat.Coprime (t i) W) := by
      intro h
      exact hi (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    have hzero : harmonicNatLaw (X i) W (t i) = 0 := by
      simp [harmonicNatLaw, hcond]
    have hprod : (∏ j : Fin k, harmonicNatLaw (X j) W (t j)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [hprod]
  unfold harmonicProductLaw
  rw [tsum_eq_sum hsupp]
  rw [Finset.sum_image (s := Finset.univ) (g := rawMap)
    (f := fun t : Fin k → ℕ =>
      (if (∏ i, t i) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (X i) W (t i)) hinj.injOn]

theorem harmonicProductLaw_support {k W : ℕ} (X : Fin k → ℕ) (σ : ℕ)
    (hσ : harmonicProductLaw W X σ ≠ 0) :
    ∃ t : ∀ i : Fin k,
        {x : ℕ // x ∈ (Finset.Ico (X i) ((X i) ^ 2)).filter (fun x => Nat.Coprime x W)},
      (∏ i, (t i).val) = σ ∧
      ∀ i, harmonicNatLaw (X i) W (t i).val ≠ 0 := by
  classical
  rw [harmonicProductLaw_eq_subtype_sum X σ] at hσ
  by_contra h
  push_neg at h
  have hsum :
      (∑ t : ∀ i : Fin k,
        {x : ℕ // x ∈ (Finset.Ico (X i) ((X i) ^ 2)).filter (fun x => Nat.Coprime x W)},
        (if (∏ i, (t i).val) = σ then 1 else 0) *
          ∏ i, harmonicNatLaw (X i) W (t i).val) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases heq : (∏ i, (t i).val) = σ
    · obtain ⟨i, hi⟩ := h t heq
      have hzero : harmonicNatLaw (X i) W (t i).val = 0 := by simpa using hi
      have hprod : (∏ j, harmonicNatLaw (X j) W (t j).val) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [heq, hprod]
    · simp [heq]
  exact hσ hsum

theorem harmonicProductLaw_support_facts {k W : ℕ} (X : Fin k → ℕ) (σ : ℕ)
    (hσ : harmonicProductLaw W X σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ ∏ i, (X i) ^ 2 ∧ Nat.Coprime σ W := by
  classical
  obtain ⟨t, hprod, hlaw⟩ := harmonicProductLaw_support X σ hσ
  have hcoord (i : Fin k) : X i ≤ (t i).val ∧ (t i).val < (X i) ^ 2 ∧
      Nat.Coprime (t i).val W := by
    by_contra hn
    have hz : harmonicNatLaw (X i) W (t i).val = 0 := by
      simp [harmonicNatLaw, hn]
    exact hlaw i hz
  have hge (i : Fin k) : 1 ≤ (t i).val := by
    have hXi : 0 < X i := by
      by_contra hn
      have hzero : X i = 0 := Nat.eq_zero_of_not_pos hn
      have hlt : (t i).val < (X i) ^ 2 := (hcoord i).2.1
      simp [hzero] at hlt
    exact le_trans (Nat.succ_le_iff.mpr hXi) (hcoord i).1
  have hprodGe : (1 : ℕ) ≤ ∏ i, (t i).val := by
    calc
      _ = ∏ _i : Fin k, (1 : ℕ) := by simp
      _ ≤ ∏ i, (t i).val := by
        apply Finset.prod_le_prod
        intro i hi
        exact hge i
  have hprodLe : ∏ i, (t i).val ≤ ∏ i, (X i) ^ 2 := by
    apply Finset.prod_le_prod
    intro i hi
    exact (hcoord i).2.1.le
  have hcop : Nat.Coprime (∏ i, (t i).val) W := by
    rw [Nat.coprime_prod_left_iff]
    intro i hi
    exact (hcoord i).2.2
  rw [hprod] at hprodGe hprodLe hcop
  exact ⟨hprodGe, hprodLe, hcop⟩

theorem divisorTemplateLaw_support_facts {n b : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (D : DivisorTemplate n b)
    (σ : ℕ) (hσ : divisorTemplateLaw A N D σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ ∏ i : Fin D.arity, (A.X N (D.cutoff i)) ^ 2 ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  unfold divisorTemplateLaw at hσ
  exact harmonicProductLaw_support_facts
    (fun i : Fin D.arity => A.X N (D.cutoff i)) σ hσ

theorem parameterTailProductLaw_eq_tailSubtypeSum {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) (σ : ℕ) :
    parameterTailProductLaw A N T σ =
      ∑ x : ∀ j : {i // i ∈ T},
          {z : ℕ // z ∈ (Finset.Ico (A.X N j.1) ((A.X N j.1) ^ 2)).filter
            (fun z => Nat.Coprime z (primorial (N + 1)))},
        (if (∏ j : {i // i ∈ T}, (x j).val) = σ then 1 else 0) *
          ∏ j : {i // i ∈ T}, harmonicNatLaw (A.X N j.1)
            (primorial (N + 1)) (x j).val := by
  classical
  let W := primorial (N + 1)
  let I : Fin n → Finset ℕ := fun i =>
    (Finset.Ico (A.X N i) ((A.X N i) ^ 2)).filter fun z => Nat.Coprime z W
  let β : Fin n → Type := fun i => {z : ℕ // z ∈ I i}
  let V := ∀ i, β i
  let rawMap (x : V) : Fin n → ℕ := fun i => (x i).val
  let support : Finset (Fin n → ℕ) := Finset.univ.image rawMap
  let term (t : Fin n → ℕ) :=
    (if (∏ j ∈ T, t j) = σ then 1 else 0) *
      ∏ i, harmonicNatLaw (A.X N i) W (t i)
  let P : Fin n → Prop := fun i => i ∈ T
  let tail := ∀ i : {i // P i}, β i.1
  let rest := ∀ i : {i // ¬ P i}, β i.1
  let e : V ≃ tail × rest := Equiv.piEquivPiSubtypeProd P β
  let tailTerm (x : tail) :=
    (if (∏ j : {i // P i}, (x j).val) = σ then 1 else 0) *
      ∏ j : {i // P i}, harmonicNatLaw (A.X N j.1) W (x j).val
  let restTerm (y : rest) :=
    ∏ j : {i // ¬ P i}, harmonicNatLaw (A.X N j.1) W (y j).val
  have hWpos : 0 < W := by
    dsimp [W]
    exact primorial_pos _
  have hinj : Function.Injective rawMap := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  have hsupp : ∀ t ∉ support, term t = 0 := by
    intro t ht
    have hnotall : ∃ i, t i ∉ I i := by
      by_contra h
      push_neg at h
      apply ht
      refine Finset.mem_image.mpr
        ⟨(fun i : Fin n => (⟨t i, h i⟩ : β i)), Finset.mem_univ _, ?_⟩
      funext i
      rfl
    obtain ⟨i, hi⟩ := hnotall
    have hcond : ¬ (A.X N i ≤ t i ∧ t i < (A.X N i) ^ 2 ∧ Nat.Coprime (t i) W) := by
      intro h
      exact hi (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    have hz : harmonicNatLaw (A.X N i) W (t i) = 0 := by
      simp [harmonicNatLaw, hcond]
    have hzProd : (∏ j, harmonicNatLaw (A.X N j) W (t j)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    simp [term, hzProd]
  have hcoord (i : Fin n) : ∑ z : β i, harmonicNatLaw (A.X N i) W z.val = 1 := by
    change ∑ z ∈ (I i).attach, harmonicNatLaw (A.X N i) W z.val = 1
    rw [Finset.sum_attach]
    simpa [I] using
      (harmonicNatLaw_sum_units (X := A.X N i) (W := W) hWpos (hX i))
  have hrest : ∑ y : rest, restTerm y = 1 := by
    have hPi :
        Fintype.piFinset (fun i : {i // ¬ P i} => (Finset.univ : Finset (β i.1))) =
          (Finset.univ : Finset rest) := by
      ext y
      simp [Fintype.mem_piFinset]
    change (∑ y ∈ (Finset.univ : Finset rest), restTerm y) = 1
    rw [← hPi]
    let box : ∀ i : {i // ¬ P i}, Finset (β i.1) := fun _ => Finset.univ
    have hprodSum := Finset.prod_univ_sum box
      (fun i z => harmonicNatLaw (A.X N i.1) W z.val)
    rw [hPi] at hprodSum
    calc
      ∑ y ∈ Finset.univ, restTerm y =
          ∏ i : {i // ¬ P i}, ∑ z : β i.1, harmonicNatLaw (A.X N i.1) W z.val := by
        simpa [restTerm] using hprodSum.symm
      _ = ∏ _i : {i // ¬ P i}, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hcoord i.1
      _ = 1 := by simp
  have hsplit (x : tail) (y : rest) :
      term (rawMap (e.symm (x, y))) = tailTerm x * restTerm y := by
    have hP (i : {i // P i}) : (e.symm (x, y) i.1).val = (x i).val := by
      have hi : P i.1 := i.property
      simp [e, Equiv.piEquivPiSubtypeProd, P, hi]
    have hN (i : {i // ¬ P i}) : (e.symm (x, y) i.1).val = (y i).val := by
      have hi : ¬ P i.1 := i.property
      simp [e, Equiv.piEquivPiSubtypeProd, P, hi]
    let g : Fin n → ℝ := fun i => harmonicNatLaw (A.X N i) W
      (rawMap (e.symm (x, y)) i)
    have hp : ∏ i ∈ Finset.univ.filter P, g i =
        ∏ i : {i // P i}, harmonicNatLaw (A.X N i.1) W (x i).val := by
      change ∏ i ∈ Finset.univ.filter (fun i : Fin n => i ∈ T), g i = _
      rw [Finset.filter_univ_mem T, ← Finset.prod_coe_sort]
      apply Fintype.prod_congr
      intro i
      simpa [g, rawMap] using
        congrArg (fun z => harmonicNatLaw (A.X N i.1) W z) (hP i)
    have hn : ∏ i ∈ Finset.univ.filter (¬ P ·), g i =
        ∏ i : {i // ¬ P i}, harmonicNatLaw (A.X N i.1) W (y i).val := by
      change ∏ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ T), g i = _
      have hU : Finset.univ.filter (fun i : Fin n => i ∉ T) = Finset.univ \ T := by
        ext i
        simp
      rw [hU, ← Finset.prod_coe_sort]
      let toRest : {i : Fin n // i ∈ Finset.univ \ T} → {i : Fin n // ¬ P i} :=
        fun i => ⟨i.1, by
          have hi : i.1 ∉ T := (Finset.mem_sdiff.mp i.2).2
          simpa [P] using hi⟩
      let fromRest : {i : Fin n // ¬ P i} → {i : Fin n // i ∈ Finset.univ \ T} :=
        fun i => ⟨i.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, by simpa [P] using i.2⟩⟩
      let eU : {i : Fin n // i ∈ Finset.univ \ T} ≃ {i : Fin n // ¬ P i} :=
        { toFun := toRest
          invFun := fromRest
          left_inv := by intro i; apply Subtype.ext; rfl
          right_inv := by intro i; apply Subtype.ext; rfl }
      calc
        (∏ i : {i // i ∈ Finset.univ \ T}, g i.1) =
            ∏ i : {i // ¬ P i}, g (eU.symm i).1 := by
          exact Fintype.prod_equiv eU (fun i => g i.1)
            (fun i => g (eU.symm i).1) (by intro i; rfl)
        _ = _ := by
          apply Fintype.prod_congr
          intro i
          have hval : (eU.symm i).1 = i.1 := by
            rfl
          rw [hval]
          simpa [g, rawMap] using
            congrArg (fun z => harmonicNatLaw (A.X N i.1) W z) (hN i)
    have hprod :
        (∏ i, harmonicNatLaw (A.X N i) W (rawMap (e.symm (x, y)) i)) =
          (∏ i : {i // P i}, harmonicNatLaw (A.X N i.1) W (x i).val) *
            ∏ i : {i // ¬ P i}, harmonicNatLaw (A.X N i.1) W (y i).val := by
      calc
        _ = (∏ i ∈ Finset.univ.filter P, g i) *
              ∏ i ∈ Finset.univ.filter (¬ P ·), g i :=
                (Finset.prod_filter_mul_prod_filter_not Finset.univ P g).symm
        _ = _ := by rw [hp, hn]
    have htailprod :
        (∏ j ∈ T, rawMap (e.symm (x, y)) j) =
          ∏ j : {i // P i}, (x j).val := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro j hj
      simpa [rawMap] using hP j
    change (if (∏ j ∈ T, rawMap (e.symm (x, y)) j) = σ then 1 else 0) *
        ∏ i, harmonicNatLaw (A.X N i) W (rawMap (e.symm (x, y)) i) = _
    rw [htailprod, hprod]
    dsimp [tailTerm, restTerm]
    ring
  have hsumImage : parameterTailProductLaw A N T σ = ∑ x : V, term (rawMap x) := by
    unfold parameterTailProductLaw
    rw [tsum_eq_sum hsupp]
    rw [Finset.sum_image (s := Finset.univ) (g := rawMap) (f := term) hinj.injOn]
  have hReindex :
      (∑ x : V, term (rawMap x)) =
        ∑ p : tail × rest, term (rawMap (e.symm p)) := by
    symm
    exact Fintype.sum_equiv e.symm (fun p => term (rawMap (e.symm p)))
      (fun x => term (rawMap x)) (fun _ => rfl)
  have hFactor :
      (∑ p : tail × rest, term (rawMap (e.symm p))) =
        (∑ x : tail, tailTerm x) * (∑ y : rest, restTerm y) := by
    calc
      _ = ∑ x : tail, ∑ y : rest, tailTerm x * restTerm y := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hsplit x y
      _ = (∑ x : tail, tailTerm x) * (∑ y : rest, restTerm y) := by
        symm
        calc
          (∑ x : tail, tailTerm x) * (∑ y : rest, restTerm y) =
              ∑ x : tail, tailTerm x * (∑ y : rest, restTerm y) := by rw [Finset.sum_mul]
          _ = ∑ x : tail, ∑ y : rest, tailTerm x * restTerm y := by
            apply Fintype.sum_congr
            intro x
            rw [Finset.mul_sum]
  rw [hsumImage, hReindex, hFactor, hrest]
  simp only [mul_one]
  apply Fintype.sum_congr
  intro x
  have hattach : (Finset.univ : Finset {i // P i}) = T.attach := by
    simpa [P] using (Finset.attach_eq_univ (s := T)).symm
  have hprodEq :
      (∏ j : {i // P i}, (x j).val) = ∏ j ∈ T.attach, (x j).val := by
    change Finset.prod (Finset.univ : Finset {i // P i}) (fun j => (x j).val) =
      Finset.prod T.attach (fun j => (x j).val)
    rw [hattach]
  have hweightEq :
      (∏ j : {i // P i}, harmonicNatLaw (A.X N j.1) W (x j).val) =
        ∏ j ∈ T.attach, harmonicNatLaw (A.X N j.1) W (x j).val := by
    change Finset.prod (Finset.univ : Finset {i // P i})
        (fun j => harmonicNatLaw (A.X N j.1) W (x j).val) =
      Finset.prod T.attach (fun j => harmonicNatLaw (A.X N j.1) W (x j).val)
    rw [hattach]
  by_cases hx : (∏ j : {i // P i}, (x j).val) = σ
  · have hb : (∏ j ∈ T.attach, (x j).val) = σ := by
      calc
        _ = ∏ j : {i // P i}, (x j).val := hprodEq.symm
        _ = σ := hx
    simp [tailTerm, hx, hb]
    exact hweightEq
  · have hb : (∏ j ∈ T.attach, (x j).val) ≠ σ := by
      intro hb
      exact hx (hprodEq ▸ hb)
    simp [tailTerm, hx, hb]

theorem parameterTailProductLaw_eq_divisorTemplateLaw {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) :
    parameterTailProductLaw A N T =
      divisorTemplateLaw A N (tailDivisorTemplate T) := by
  classical
  let W := primorial (N + 1)
  let eT : T ≃ Fin T.card := T.equivFinOfCardEq rfl
  let Xfin : Fin T.card → ℕ := fun i => A.X N (eT.symm i).1
  let I : Fin n → Finset ℕ := fun j =>
    (Finset.Ico (A.X N j) ((A.X N j) ^ 2)).filter (fun z => Nat.Coprime z W)
  let β : Fin n → Type := fun j => {z : ℕ // z ∈ I j}
  letI : ∀ j : Fin n, Fintype (β j) := fun j => Finset.Subtype.fintype (I j)
  let Tail := ∀ j : T, β j.1
  let FinTail := ∀ i : Fin T.card, β (eT.symm i).1
  letI : Fintype Tail := Pi.instFintype
  letI : Fintype FinTail := Pi.instFintype
  let ePi : Tail ≃ FinTail := Equiv.piCongrLeft' (fun j : T => β j.1) eT
  funext σ
  rw [parameterTailProductLaw_eq_tailSubtypeSum A N T hX σ]
  unfold divisorTemplateLaw
  change (∑ x : Tail,
      (if (∏ j : T, (x j).val) = σ then 1 else 0) *
        ∏ j : T, harmonicNatLaw (A.X N j.1) W (x j).val) =
    harmonicProductLaw W Xfin σ
  rw [harmonicProductLaw_eq_subtype_sum Xfin σ]
  apply Fintype.sum_equiv ePi
  intro x
  have hval (j : T) : (ePi x (eT j)).val = (x j).val := by
    calc
      _ = (x (eT.symm (eT j))).val := by simp [ePi, Equiv.piCongrLeft']
      _ = (x j).val := by rw [eT.symm_apply_apply]
  have hXval (j : T) : Xfin (eT j) = A.X N j.1 := by
    dsimp [Xfin]
    rw [eT.symm_apply_apply]
  have hprod : (∏ j : T, (x j).val) = ∏ i : Fin T.card, (ePi x i).val := by
    exact Fintype.prod_equiv eT (fun j => (x j).val)
      (fun i => (ePi x i).val) (fun j => (hval j).symm)
  have hlaw :
      (∏ j : T, harmonicNatLaw (A.X N j.1) W (x j).val) =
        ∏ i : Fin T.card,
          harmonicNatLaw (Xfin i) W (ePi x i).val := by
    exact Fintype.prod_equiv eT
      (fun j => harmonicNatLaw (A.X N j.1) W (x j).val)
      (fun i => harmonicNatLaw (Xfin i) W (ePi x i).val)
      (fun j => by rw [hXval j, hval j])
  have hattach : (Finset.univ : Finset T) = T.attach :=
    (Finset.attach_eq_univ (s := T)).symm
  have hprodAttach :
      (∏ j ∈ T.attach, (x j).val) = ∏ i : Fin T.card, (ePi x i).val := by
    calc
      _ = ∏ j : T, (x j).val := by
        change Finset.prod T.attach (fun j => (x j).val) =
          Finset.prod (Finset.univ : Finset T) (fun j => (x j).val)
        rw [← hattach]
      _ = _ := hprod
  have hlawAttach :
      (∏ j ∈ T.attach, harmonicNatLaw (A.X N j.1) W (x j).val) =
        ∏ i : Fin T.card, harmonicNatLaw (Xfin i) W (ePi x i).val := by
    calc
      _ = ∏ j : T, harmonicNatLaw (A.X N j.1) W (x j).val := by
        change Finset.prod T.attach (fun j => harmonicNatLaw (A.X N j.1) W (x j).val) =
          Finset.prod (Finset.univ : Finset T)
            (fun j => harmonicNatLaw (A.X N j.1) W (x j).val)
        rw [← hattach]
      _ = _ := hlaw
  simp [hprodAttach, hlawAttach]

theorem parameterTailProductLaw_support_facts {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) (σ : ℕ)
    (hσ : parameterTailProductLaw A N T σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ ∏ j : T, (A.X N j.1) ^ 2 ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  classical
  rw [parameterTailProductLaw_eq_divisorTemplateLaw A N T hX] at hσ
  have hdiv := divisorTemplateLaw_support_facts A N (tailDivisorTemplate T) σ hσ
  let eT : T ≃ Fin T.card := T.equivFinOfCardEq rfl
  have hprodEq :
      (∏ j : T, (A.X N j.1) ^ 2) =
        ∏ i : Fin T.card, (A.X N (eT.symm i).1) ^ 2 := by
    exact Fintype.prod_equiv eT
      (fun j : T => (A.X N j.1) ^ 2)
      (fun i : Fin T.card => (A.X N (eT.symm i).1) ^ 2)
      (fun j => by simp [eT])
  have hupper : σ ≤ ∏ i : Fin T.card, (A.X N (eT.symm i).1) ^ 2 := by
    exact hdiv.2.1
  exact ⟨hdiv.1, hupper.trans_eq hprodEq.symm, hdiv.2.2⟩

theorem chainTailProductLaw_support_facts {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ) (k : Fin m)
    (σ : ℕ)
    (hσ : parameterTailProductLaw S.core.parameters N (C.block k).2.val σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ masterScaleV S.core.parameters N C.gap ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  classical
  let T := (C.block k).2.val
  have hX (i : Fin K) : 4 * primorial (N + 1) ≤ S.core.parameters.X N i :=
    S.gapStage.valid_raw_cutoffs N i
  have htail := parameterTailProductLaw_support_facts
    S.core.parameters N T hX σ hσ
  have hprodEquiv : (∏ j : T, (S.core.parameters.X N j.1) ^ 2) =
      ∏ j ∈ T, (S.core.parameters.X N j) ^ 2 := by
    exact Finset.prod_coe_sort T (fun j : Fin K => (S.core.parameters.X N j) ^ 2)
  have hupperT : σ ≤ ∏ j ∈ T, (S.core.parameters.X N j) ^ 2 := by
    calc
      σ ≤ ∏ j : T, (S.core.parameters.X N j.1) ^ 2 := htail.2.1
      _ = ∏ j ∈ T, (S.core.parameters.X N j) ^ 2 := hprodEquiv
  let U : Finset (Fin K) := Finset.univ.filter (fun j => j < C.gap)
  have hsub : T ⊆ U := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, C.tails_before_gap k j hj⟩
  have hone (j : Fin K) (_hj : j ∈ U) : 1 ≤ (S.core.parameters.X N j) ^ 2 := by
    have hXj := hX j
    have hWpos : 0 < primorial (N + 1) := primorial_pos _
    have hXone : 1 ≤ S.core.parameters.X N j := by omega
    exact Nat.one_le_pow 2 (S.core.parameters.X N j) hXone
  have hprodSub :
      (∏ j ∈ T, (S.core.parameters.X N j) ^ 2) ≤
        ∏ j ∈ U, (S.core.parameters.X N j) ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le hsub
      (by intro j hjU hjnot; exact hone j hjU)
  have hUle :
      (∏ j ∈ U, (S.core.parameters.X N j) ^ 2) ≤
    masterScaleV S.core.parameters N C.gap := by
    unfold masterScaleV
    simp [U]
  exact ⟨htail.1, le_trans hupperT (le_trans hprodSub hUle), htail.2.2⟩

theorem weighted_variance_identity (b h c : ℝ) :
    b * h ^ 2 - (2 * c) * (b * h) + c ^ 2 * b = b * (h - c) ^ 2 := by
  ring

/-- Expand a finite product of `1 + f` into its subset moments. -/
theorem prod_one_add_eq_powerset_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  exact Finset.prod_one_add s

/-- Limits commute with a fixed finite sum. -/
theorem tendsto_finset_sum_of_pointwise {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ → ℝ) (g : α → ℝ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (g i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (𝓝 (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- If every subset term has limit one, their sum has the expected power-of-two limit. -/
theorem tendsto_powerset_sum_of_tendsto_one {α : Type*} [DecidableEq α]
    (s : Finset α) (E : ℕ → Finset α → ℝ)
    (hE : ∀ t ∈ s.powerset, Tendsto (fun n => E n t) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ t ∈ s.powerset, E n t) atTop (𝓝 ((2 : ℝ) ^ s.card)) := by
  have hsum := tendsto_finset_sum_of_pointwise s.powerset
    (fun t n => E n t) (fun _ => (1 : ℝ)) hE
  simpa [Finset.card_powerset] using hsum

/-- The three auxiliary moments force the weighted square error to tend to zero. -/
theorem tendsto_weighted_variance_from_moments
    (E0 E1 E2 : ℕ → ℝ) (a c : ℝ)
    (h0 : Tendsto E0 atTop (𝓝 a))
    (h1 : Tendsto E1 atTop (𝓝 (a * c)))
    (h2 : Tendsto E2 atTop (𝓝 (a * c ^ 2))) :
    Tendsto (fun n => E2 n - (2 * c) * E1 n + c ^ 2 * E0 n) atTop (𝓝 0) := by
  have hlin : Tendsto
      (fun n => E2 n - (2 * c) * E1 n + c ^ 2 * E0 n) atTop
      (𝓝 (a * c ^ 2 - (2 * c) * (a * c) + c ^ 2 * a)) := by
    exact (h2.sub (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))
  convert hlin using 1 <;> ring_nf

theorem SuperPolynomialSmall.tendsto_mul_nat_pow {e V : ℕ → ℝ}
    (hsmall : SuperPolynomialSmall e V) (hV : Tendsto V atTop atTop) (q : ℕ) :
    Tendsto (fun n => V n ^ q * e n) atTop (𝓝 0) := by
  by_cases hq : q = 0
  · subst q
    have hEV : Tendsto (fun n => e n * V n) atTop (𝓝 0) := by
      simpa using hsmall 1 (by norm_num)
    have hVinv : Tendsto (fun n => (V n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hV
    have hmul : Tendsto (fun n => e n * V n * (V n)⁻¹) atTop (𝓝 0) := by
      simpa using hEV.mul hVinv
    have hpos : ∀ᶠ n in atTop, 0 < V n := by
      filter_upwards [hV.eventually_ge_atTop 1] with n hn
      linarith
    have heq : (fun n => e n) =ᶠ[atTop] fun n => e n * V n * (V n)⁻¹ := by
      filter_upwards [hpos] with n hn
      field_simp [ne_of_gt hn]
    simpa [pow_zero] using (tendsto_congr' heq).2 hmul
  · have hqpos : (q : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero hq
    simpa [Real.rpow_natCast, mul_comm] using hsmall (q : ℝ) hqpos

theorem superPolynomialSmall_fintype_sum {ι : Type*} [Fintype ι]
    (e : ι → ℕ → ℝ) (V : ℕ → ℝ)
    (hsmall : ∀ i, SuperPolynomialSmall (e i) V) :
    SuperPolynomialSmall (fun N => ∑ i, e i N) V := by
  intro C hC
  have hsum : Tendsto (fun N => ∑ i : ι, e i N * V N ^ C) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (s := Finset.univ)
      (f := fun i N => e i N * V N ^ C) (a := fun _ : ι => (0 : ℝ))
      (fun i hi => hsmall i C hC)
    simpa using h
  have hcongr : (fun N => (∑ i, e i N) * V N ^ C) =ᶠ[atTop]
      fun N => ∑ i : ι, e i N * V N ^ C := by
    filter_upwards [] with N
    rw [Finset.sum_mul]
  exact (tendsto_congr' hcongr).2 hsum


theorem weightedLinearFormsError_tendsto {n q d b m : ℕ} {Aset : Finset ℚ}
    {tests : Finset (IntegerPolynomial m)} {S : FromArithmetic.MasterScales n Aset m tests}
    (D : FromArithmetic.WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    Tendsto (fun N : ℕ => 1 / ((N + 1 : ℕ) : ℝ) + (D.V N : ℝ) ^ q *
      (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
  have hV : Tendsto (fun N => (D.V N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.V_tendsto
  have hbase := SuperPolynomialSmall.tendsto_mul_nat_pow
    D.epsilonBase_superpolynomial hV q
  have hcrt := SuperPolynomialSmall.tendsto_mul_nat_pow
    D.epsilonCRT_superpolynomial hV q
  have hsum : Tendsto (fun N => (D.V N : ℝ) ^ q *
      (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
    simpa [mul_add] using hbase.add hcrt
  have hrecip : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hrecip.add hsum

theorem weightedLinearFormsAverage_tendsto_of_eventProbability
    {n q d b m : ℕ} {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : FromArithmetic.MasterScales n Aset m tests}
    (D : FromArithmetic.WeightedLinearFormsData (q := q) (d := d) (b := b) S)
    (E : ℕ → (Fin m → ℕ) → Prop) (c : ℝ)
    (hE : ∀ᶠ N in atTop, ∀ p, E N p → D.goodDomain N p)
    (hprob : Tendsto (fun N => FromArithmetic.weightedLinearFormsEventProbability D N (E N))
      atTop (𝓝 c)) :
    Tendsto (fun N => FromArithmetic.weightedLinearFormsAverage D N (E N)) atTop (𝓝 c) := by
  classical
  obtain ⟨C, hC, hbound⟩ := FromArithmetic.prop_linear_forms D
  have herr := weightedLinearFormsError_tendsto D
  have habs : Tendsto
      (fun N => |FromArithmetic.weightedLinearFormsAverage D N (E N) -
        FromArithmetic.weightedLinearFormsEventProbability D N (E N)|) atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun N : ℕ => |C * (1 / ((N + 1 : ℕ) : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N))|) atTop (𝓝 0) := by
      simpa [mul_comm, Nat.cast_add] using (herr.const_mul C).abs
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => abs_nonneg _)
      ?_ hupper
    filter_upwards [hE] with N hN
    have h := hbound N (E N) (hN)
    calc
      _ ≤ C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N)) := h
      _ = C * (1 / ((N + 1 : ℕ) : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N)) := by simp
      _ ≤ |C * (1 / ((N + 1 : ℕ) : ℝ) + (D.V N : ℝ) ^ q *
          (D.epsilonBase N + D.epsilonCRT N))| := le_abs_self _
  have hdiff : Tendsto
      (fun N => FromArithmetic.weightedLinearFormsAverage D N (E N) -
        FromArithmetic.weightedLinearFormsEventProbability D N (E N)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  simpa [sub_add_cancel] using hdiff.add hprob

/-- The pointwise target-cube product is dominated by its product of weight bounds. -/
theorem target_cube_product_abs_le_targetBound
    {K m q r s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
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

namespace AdditiveMoment

abbrev RetainedIndex {m q r : ℕ} (Sh : RowShape m q r) :=
  Σ I : NonTarget Sh, ({R : NonTarget Sh // R ≠ I} → Fin 2)

abbrev Occurrence {m q r : ℕ} (Sh : RowShape m q r) :=
  (NonTarget Sh → Fin 2) ⊕ (Fin 2 × RetainedIndex Sh)

abbrev Coordinate {m q r : ℕ} (Sh : RowShape m q r) :=
  Fin m ⊕ ((NonTarget Sh × Fin 2) ⊕ Fin 2)

noncomputable def activeOccurrences {m q r : ℕ} (Sh : RowShape m q r) (k : ℕ) :
    Finset (Occurrence Sh) := by
  classical
  exact Finset.univ.filter fun o => match o with
    | .inl _ => True
    | .inr jI => jI.1.val < k

def occurrenceRow {m q r : ℕ} (Sh : RowShape m q r) (o : Occurrence Sh) : Fin r :=
  match o with
  | .inl _ => Sh.star
  | .inr jI => jI.2.1.1

noncomputable def occurrenceCoeff {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (N : ℕ) (p : Fin q → ℕ) (o : Occurrence Sh) (v : Coordinate Sh) : ℚ :=
  let c := chainScale S.core.parameters C a N
  let Mp := directionModulus S N dirs.poly p
  let I := occurrenceRow Sh o
  match v with
  | .inl k => rowTemplateCoefficient c (Sh.row I) p k
  | .inr (.inl (R, e)) =>
    match o with
    | .inl ω => if e = ω R then (Mp : ℚ) else 0
    | .inr jI =>
      if h : R ≠ jI.2.1 then
        if e = jI.2.2 ⟨R, h⟩ then
          rowForm c (Sh.row I) p (dirs.translation c Mp p R.1)
        else 0
      else 0
  | .inr (.inr j) =>
    match o with
    | .inl _ => 0
    | .inr jI => if j = jI.1 then
        rowForm c (Sh.row I) p (dirs.rootTranslation c (S.core.parameters.M N) p)
      else 0

noncomputable def occurrenceValue {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (o : Occurrence Sh) (x : Coordinate Sh → ℤ) : ℚ :=
  ∑ v, occurrenceCoeff S C a Sh dirs N p o v * (x v : ℚ)

noncomputable def coordinateLaw {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (v : Coordinate Sh) (z : ℤ) : ℝ :=
  match v with
  | .inl k => harmonicLaw
      (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) z
  | .inr (.inl _) => FromArithmetic.uniformIntegerIntervalLaw 0
      (max 1 (shiftLength S C.gap J0 N dirs.poly p)) z
  | .inr (.inr _) => FromArithmetic.uniformIntegerIntervalLaw 0
      (S.core.parameters.H N C.gap) z

theorem pkgElim_coordinateLaw_nonneg {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (v : Coordinate Sh) (z : ℤ) :
    0 ≤ coordinateLaw S C Sh dirs J0 N p v z := by
  cases v with
  | inl k =>
    change 0 ≤ harmonicLaw
      (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) z
    have hW : 0 < primorial (N + 1) := primorial_pos _
    have hX : 4 * primorial (N + 1) ≤ S.core.parameters.X N (C.block k).1 :=
      S.gapStage.valid_raw_cutoffs N (C.block k).1
    have hnormalizer : 0 < harmonicNormalizer
        (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) := by
      rw [harmonicNormalizer_eq_rawMass]
      exact OAI.RawHarmonicProbability.mass_pos _ _ hW hX
    unfold harmonicLaw
    split_ifs with h
    · have hz : 0 < (z.toNat : ℝ) := by
        have hXpos : 0 < S.core.parameters.X N (C.block k).1 := by omega
        exact_mod_cast lt_of_lt_of_le hXpos h.2.1
      positivity
    · positivity
  | inr v =>
    cases v with
    | inl old =>
      change 0 ≤ FromArithmetic.uniformIntegerIntervalLaw 0
        (max 1 (shiftLength S C.gap J0 N dirs.poly p)) z
      unfold FromArithmetic.uniformIntegerIntervalLaw
      split_ifs <;> positivity
    | inr root =>
      change 0 ≤ FromArithmetic.uniformIntegerIntervalLaw 0
        (S.core.parameters.H N C.gap) z
      unfold FromArithmetic.uniformIntegerIntervalLaw
      split_ifs <;> positivity

noncomputable def coordinateProductLaw {K m q r s d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (eX : Coordinate Sh ≃ Fin d) (x : Fin d → ℤ) : ℝ :=
  ∏ i : Fin d, coordinateLaw S C Sh dirs J0 N p (eX.symm i) (x i)

theorem pkgElim_coordinateProductLaw_nonneg {K m q r s d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (eX : Coordinate Sh ≃ Fin d) (x : Fin d → ℤ) :
    0 ≤ coordinateProductLaw S C Sh dirs J0 N p eX x := by
  unfold coordinateProductLaw
  apply Finset.prod_nonneg
  intro i hi
  exact pkgElim_coordinateLaw_nonneg S C Sh dirs J0 N p (eX.symm i) (x i)

noncomputable def pkgElim_coordinateSupport {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (v : Coordinate Sh) : Finset ℤ :=
  match v with
  | .inl k => Finset.Ico (S.core.parameters.X N (C.block k).1 : ℤ)
      ((S.core.parameters.X N (C.block k).1 ^ 2 : ℕ) : ℤ)
  | .inr (.inl _) => Finset.Ico 0
      ((max 1 (shiftLength S C.gap J0 N dirs.poly p) : ℕ) : ℤ)
  | .inr (.inr _) => Finset.Ico 0 (S.core.parameters.H N C.gap : ℤ)

theorem pkgElim_coordinateLaw_zero_of_not_mem {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (v : Coordinate Sh) (z : ℤ)
    (hz : z ∉ pkgElim_coordinateSupport S C Sh dirs J0 N p v) :
    coordinateLaw S C Sh dirs J0 N p v z = 0 := by
  cases v with
  | inl k =>
    change harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1)) z = 0
    change z ∉ Finset.Ico (S.core.parameters.X N (C.block k).1 : ℤ)
      ((S.core.parameters.X N (C.block k).1 ^ 2 : ℕ) : ℤ) at hz
    unfold harmonicLaw
    rw [if_neg]
    intro h
    apply hz
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h.1
    have hlow : (S.core.parameters.X N (C.block k).1 : ℤ) ≤ z := by
      calc
        _ ≤ (z.toNat : ℤ) := by exact_mod_cast h.2.1
        _ = z := hcast
    have hhigh : z <
        ((S.core.parameters.X N (C.block k).1 ^ 2 : ℕ) : ℤ) := by
      calc
        z = (z.toNat : ℤ) := hcast.symm
        _ < _ := by exact_mod_cast h.2.2.1
    exact Finset.mem_Ico.mpr ⟨hlow, hhigh⟩
  | inr v =>
    cases v with
    | inl old =>
      change FromArithmetic.uniformIntegerIntervalLaw 0
        (max 1 (shiftLength S C.gap J0 N dirs.poly p)) z = 0
      change z ∉ Finset.Ico 0
        ((max 1 (shiftLength S C.gap J0 N dirs.poly p) : ℕ) : ℤ) at hz
      unfold FromArithmetic.uniformIntegerIntervalLaw
      rw [if_neg]
      intro h
      apply hz
      exact Finset.mem_Ico.mpr (by simpa using h)
    | inr root =>
      change FromArithmetic.uniformIntegerIntervalLaw 0
        (S.core.parameters.H N C.gap) z = 0
      change z ∉ Finset.Ico 0 (S.core.parameters.H N C.gap : ℤ) at hz
      unfold FromArithmetic.uniformIntegerIntervalLaw
      rw [if_neg]
      intro h
      apply hz
      exact Finset.mem_Ico.mpr (by simpa using h)

theorem pkgElim_coordinateLaw_tsum_one {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (v : Coordinate Sh) :
    ∑' z : ℤ, coordinateLaw S C Sh dirs J0 N p v z = 1 := by
  cases v with
  | inl k =>
    simpa [coordinateLaw] using pkgElim_harmonicLaw_tsum_one (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block k).1)
  | inr v =>
    cases v with
    | inl old =>
      apply uniformIntegerIntervalLaw_tsum_one
      exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
    | inr root =>
      exact uniformIntegerIntervalLaw_tsum_one (S.core.parameters.Hpos N C.gap)

theorem pkgElim_coordinateProductLaw_tsum_one {K m q r s d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (J0 N : ℕ)
    (p : Fin q → ℕ) (eX : Coordinate Sh ≃ Fin d) :
    ∑' x : Fin d → ℤ, coordinateProductLaw S C Sh dirs J0 N p eX x = 1 := by
  classical
  let μ : Fin d → ℤ → ℝ := fun i => coordinateLaw S C Sh dirs J0 N p (eX.symm i)
  let T : Fin d → Finset ℤ := fun i => pkgElim_coordinateSupport S C Sh dirs J0 N p (eX.symm i)
  have hsupp : ∀ i z, z ∉ T i → μ i z = 0 := by
    intro i z hz
    exact pkgElim_coordinateLaw_zero_of_not_mem S C Sh dirs J0 N p (eX.symm i) z hz
  have hnorm (i : Fin d) : ∑ z ∈ T i, μ i z = 1 := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (f := μ i) (s := T i) (fun z hz => hsupp i z hz)]
    exact pkgElim_coordinateLaw_tsum_one S C Sh dirs J0 N p (eX.symm i)
  simpa [coordinateProductLaw, μ] using
    (productLaw_tsum_one_of_finite_support μ T hsupp hnorm)

noncomputable def occurrenceDivisorTemplate {K m q r : ℕ}
    (C : MasterChain K m) (Sh : RowShape m q r) (o : Occurrence Sh) :
    DivisorTemplate K K :=
  tailDivisorTemplate ((C.block (Sh.row (occurrenceRow Sh o)).anchor).2.val)

theorem pkgElim_occurrenceDivisorTemplateLaw_eq {K m q r s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (o : Occurrence Sh) (N σ : ℕ) :
    divisorTemplateLaw S.core.parameters N (occurrenceDivisorTemplate C Sh o) σ =
      parameterTailProductLaw S.core.parameters N
        (C.block (Sh.row (occurrenceRow Sh o)).anchor).2.val σ := by
  unfold occurrenceDivisorTemplate
  rw [parameterTailProductLaw_eq_divisorTemplateLaw S.core.parameters N
    ((C.block (Sh.row (occurrenceRow Sh o)).anchor).2.val)
    (fun j => S.gapStage.valid_raw_cutoffs N j)]

theorem pkgElim_selectedOccurrenceDivisor_support {K m q r s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (o : Occurrence Sh) (N σ : ℕ)
    (hσ : divisorTemplateLaw S.core.parameters N (occurrenceDivisorTemplate C Sh o) σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ masterScaleV S.core.parameters N C.gap ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  rw [pkgElim_occurrenceDivisorTemplateLaw_eq S C Sh o N] at hσ
  exact chainTailProductLaw_support_facts S C N
    (Sh.row (occurrenceRow Sh o)).anchor σ hσ

def emptyDivisorTemplate (K : ℕ) : DivisorTemplate K K where
  arity := 0
  arity_le := Nat.zero_le K
  cutoff := Fin.elim0

noncomputable def pkgElim_momentDivisorTemplate {K m q r h : ℕ}
    (C : MasterChain K m) (Sh : RowShape m q r)
    (eO : Occurrence Sh ≃ Fin h) (F : Finset (Occurrence Sh)) :
    Fin h → DivisorTemplate K K := fun u =>
      if eO.symm u ∈ F then occurrenceDivisorTemplate C Sh (eO.symm u)
      else emptyDivisorTemplate K

theorem pkgElim_momentDivisorTemplate_support {K m q r h s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (eO : Occurrence Sh ≃ Fin h)
    (F : Finset (Occurrence Sh)) (N : ℕ) (u : Fin h) (σ : ℕ)
    (hσ : FromArithmetic.divisorTemplateLaw S.core.parameters N
      (pkgElim_momentDivisorTemplate C Sh eO F u) σ ≠ 0) :
    1 ≤ σ ∧ σ ≤ masterScaleV S.core.parameters N C.gap ∧
      Nat.Coprime σ (primorial (N + 1)) := by
  classical
  by_cases hF : eO.symm u ∈ F
  · have hσ' : FromArithmetic.divisorTemplateLaw S.core.parameters N
        (occurrenceDivisorTemplate C Sh (eO.symm u)) σ ≠ 0 := by
      simpa [pkgElim_momentDivisorTemplate, hF] using hσ
    exact pkgElim_selectedOccurrenceDivisor_support S C Sh (eO.symm u) N σ hσ'
  · have hσ' : FromArithmetic.divisorTemplateLaw S.core.parameters N
        (emptyDivisorTemplate K) σ ≠ 0 := by
      simpa [pkgElim_momentDivisorTemplate, hF] using hσ
    have hempty := divisorTemplateLaw_support_facts S.core.parameters N
      (emptyDivisorTemplate K) σ hσ'
    have hσone : σ ≤ 1 := by
      have hprod :
          (∏ i : Fin (emptyDivisorTemplate K).arity,
            (S.core.parameters.X N ((emptyDivisorTemplate K).cutoff i)) ^ 2) ≤ 1 := by
        change (∏ i : Fin 0, (S.core.parameters.X N (Fin.elim0 i)) ^ 2) ≤ 1
        rw [Fin.prod_univ_zero]
      exact hempty.2.1.trans hprod
    have hV : 1 ≤ masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      omega
    exact ⟨hempty.1, hσone.trans hV, hempty.2.2⟩

noncomputable def pkgElim_retainedChoice {m q r : ℕ} (Sh : RowShape m q r)
    (I : NonTarget Sh) (η : {R : NonTarget Sh // R ≠ I} → Fin 2)
    (R : NonTarget Sh) : Fin 2 := by
  classical
  exact if h : R ≠ I then η ⟨R, h⟩ else 0

noncomputable def rowCoeff {K m q r s h d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (eO : Occurrence Sh ≃ Fin h)
    (eX : Coordinate Sh ≃ Fin d) :
    ℕ → (Fin s → ℕ) → Fin h → Fin d → ℚ := fun N p' u j =>
      occurrenceCoeff S C a Sh dirs N (fun i => p' (ι i))
        (eO.symm u) (eX.symm j)

theorem linearRowValue_eq_occurrenceValue {K m q r s h d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (eO : Occurrence Sh ≃ Fin h)
    (eX : Coordinate Sh ≃ Fin d) (N : ℕ) (p' : Fin s → ℕ)
    (u : Fin h) (x : Fin d → ℤ) :
    FromArithmetic.linearRowValue (rowCoeff S ι C a Sh dirs eO eX)
      N p' u x =
        occurrenceValue S C a Sh dirs N (fun i => p' (ι i)) (eO.symm u)
          (fun v => x (eX v)) := by
  classical
  unfold FromArithmetic.linearRowValue rowCoeff occurrenceValue
  exact (Fintype.sum_equiv eX
    (fun v => occurrenceCoeff S C a Sh dirs N (fun i => p' (ι i)) (eO.symm u) v *
      ((x (eX v) : ℤ) : ℚ))
    (fun j => occurrenceCoeff S C a Sh dirs N (fun i => p' (ι i))
      (eO.symm u) (eX.symm j) * (x j : ℚ))
    (by intro v; simp)).symm

noncomputable def pkgElim_expandedAuxiliaryMoment {K m q r s d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q)) (J0 : ℕ)
    (eX : Coordinate Sh ≃ Fin d) (F : Finset (Occurrence Sh)) (N : ℕ) : ℝ :=
  goodSlotAverage S C.gap N (GoodTuple S C.gap N tests dirs.poly) fun p =>
    ∑' x : Fin d → ℤ,
      coordinateProductLaw S C Sh dirs J0 N p eX x *
        ∏ o ∈ F,
          atQ (chainWeight S.core.parameters C N (Sh.row (occurrenceRow Sh o)).anchor)
            (occurrenceValue S C a Sh dirs N p o (fun v => x (eX v)))

theorem occurrenceValue_target {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (ω : NonTarget Sh → Fin 2) (x : Coordinate Sh → ℤ) :
    occurrenceValue S C a Sh dirs N p (.inl ω) x =
      rowForm (chainScale S.core.parameters C a N) (Sh.row Sh.star) p
        (fun k => (x (.inl k) : ℚ)) +
      (directionModulus S N dirs.poly p : ℚ) *
        ∑ R : NonTarget Sh, (x (.inr (.inl (R, ω R)) : Coordinate Sh) : ℚ) := by
  classical
  simp [occurrenceValue, occurrenceCoeff, occurrenceRow, rowTemplateCoefficient,
    rowForm, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Fin.sum_univ_two]
  rw [Finset.mul_sum]

theorem pkgElim_occurrencePivotContribution {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (o : Occurrence Sh) (x : Coordinate Sh → ℤ) :
    (∑ k : Fin m, occurrenceCoeff S C a Sh dirs N p o (.inl k) *
      (x (.inl k) : ℚ)) =
      rowForm (chainScale S.core.parameters C a N) (Sh.row (occurrenceRow Sh o)) p
        (fun k => (x (.inl k) : ℚ)) := by
  simp [occurrenceCoeff, occurrenceRow, rowTemplateCoefficient, rowForm]

theorem pkgElim_occurrenceRootContribution {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (j : Fin 2) (I : NonTarget Sh)
    (η : {R : NonTarget Sh // R ≠ I} → Fin 2) (x : Coordinate Sh → ℤ) :
    (∑ j' : Fin 2,
      occurrenceCoeff S C a Sh dirs N p (.inr (j, ⟨I, η⟩))
        (.inr (.inr j')) * (x (.inr (.inr j')) : ℚ)) =
      rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
        (dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p) * (x (.inr (.inr j) : Coordinate Sh) : ℚ) := by
  classical
  rw [Finset.sum_eq_single j]
  · simp [occurrenceCoeff, occurrenceRow]
  · intro j' hj' hj
    simp [occurrenceCoeff, occurrenceRow, hj]
  · simp

theorem pkgElim_occurrenceOldShiftContribution {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (j : Fin 2) (I : NonTarget Sh)
    (η : {R : NonTarget Sh // R ≠ I} → Fin 2) (x : Coordinate Sh → ℤ) :
    (∑ R : NonTarget Sh, ∑ e : Fin 2,
      occurrenceCoeff S C a Sh dirs N p (.inr (j, ⟨I, η⟩))
        (.inr (.inl (R, e))) * (x (.inr (.inl (R, e))) : ℚ)) =
      ∑ R : NonTarget Sh, if R = I then 0 else
        rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
          (dirs.translation (chainScale S.core.parameters C a N)
            (directionModulus S N dirs.poly p) p R.1) *
          (x (.inr (.inl (R, pkgElim_retainedChoice Sh I η R)) : Coordinate Sh) : ℚ) := by
  classical
  apply Finset.sum_congr rfl
  intro R hR
  by_cases h : R ≠ I
  · let e₀ := η ⟨R, h⟩
    have hcoeff (e : Fin 2) :
        occurrenceCoeff S C a Sh dirs N p (.inr (j, ⟨I, η⟩))
          (.inr (.inl (R, e))) =
        if e = e₀ then
          rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
            (dirs.translation (chainScale S.core.parameters C a N)
              (directionModulus S N dirs.poly p) p R.1)
        else 0 := by
      simp [occurrenceCoeff, occurrenceRow, e₀, h]
    calc
      _ = ∑ e : Fin 2, if e = e₀ then
            rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
              (dirs.translation (chainScale S.core.parameters C a N)
                (directionModulus S N dirs.poly p) p R.1) *
              (x (.inr (.inl (R, e)) : Coordinate Sh) : ℚ)
          else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hcoeff e]
        by_cases he₀ : e = e₀ <;> simp [he₀]
      _ = rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
            (dirs.translation (chainScale S.core.parameters C a N)
              (directionModulus S N dirs.poly p) p R.1) *
          (x (.inr (.inl (R, e₀)) : Coordinate Sh) : ℚ) := by
        rw [Finset.sum_eq_single e₀]
        · simp
        · intro e he he₀
          simp [he₀]
        · simp
      _ = if R = I then 0 else
            rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
              (dirs.translation (chainScale S.core.parameters C a N)
                (directionModulus S N dirs.poly p) p R.1) *
              (x (.inr (.inl (R, pkgElim_retainedChoice Sh I η R)) : Coordinate Sh) : ℚ) := by
        have hchoice : pkgElim_retainedChoice Sh I η R = e₀ := by
          simp [pkgElim_retainedChoice, e₀, h]
        simp [h, hchoice]
  · have hEq : R = I := by simpa using h
    simp [occurrenceCoeff, occurrenceRow, pkgElim_retainedChoice, h, hEq]

theorem pkgElim_occurrenceValue_retained {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (N : ℕ)
    (p : Fin q → ℕ) (j : Fin 2) (I : NonTarget Sh)
    (η : {R : NonTarget Sh // R ≠ I} → Fin 2) (x : Coordinate Sh → ℤ) :
    occurrenceValue S C a Sh dirs N p (.inr (j, ⟨I, η⟩)) x =
      rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
        (fun k => (x (.inl k) : ℚ)) +
      (∑ R : NonTarget Sh, if R = I then 0 else
        rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
          (dirs.translation (chainScale S.core.parameters C a N)
            (directionModulus S N dirs.poly p) p R.1) *
          (x (.inr (.inl (R, pkgElim_retainedChoice Sh I η R)) : Coordinate Sh) : ℚ)) +
      rowForm (chainScale S.core.parameters C a N) (Sh.row I.1) p
        (dirs.rootTranslation (chainScale S.core.parameters C a N)
          (S.core.parameters.M N) p) * (x (.inr (.inr j) : Coordinate Sh) : ℚ) := by
  classical
  unfold occurrenceValue
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [pkgElim_occurrencePivotContribution, pkgElim_occurrenceOldShiftContribution,
    pkgElim_occurrenceRootContribution]
  simp only [occurrenceRow]
  ring

def pkgElim_momentGlobalData {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (J0 B N : ℕ) : Prop :=
  (∃ c : Fin m → ℤ,
    (∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d) ∧
    (∀ d, 0 < c d) ∧
    (∀ u d, u < d → ∃ k : ℕ,
      c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d) ∧
    (∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))) ∧
  (∀ p, GoodTuple S C.gap N tests dirs.poly p →
    IntegerDirectionFacts S C a N dirs tests B p) ∧
  0 < primePoolMass (S.primeStage.pool N C.gap).lower
    (S.primeStage.pool N C.gap).upper ∧
  masterScaleV S.core.parameters N C.gap + 1 <
    (S.primeStage.pool N C.gap).lower ∧
  1 ≤ S.core.parameters.H N C.gap /
    (J0 * ((S.primeStage.pool N C.gap).upper +
      masterScaleV S.core.parameters N C.gap) ^ B)

theorem pkgElim_momentGlobalData_eventually {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm)
    (C : MasterChain K m) (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset)
    (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q))
    (J0 B : ℕ) (hJ0 : 0 < J0)
    (hfactsEvent : ∀ᶠ N in atTop, ∀ p, GoodTuple S C.gap N tests dirs.poly p →
      IntegerDirectionFacts S C a N dirs tests B p) :
    ∀ᶠ N in atTop, pkgElim_momentGlobalData S C a Sh dirs tests J0 B N := by
  classical
  have hcoeff : ∀ᶠ N in atTop,
      ∃ c : Fin m → ℤ,
        (∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d) ∧
        (∀ d, 0 < c d) ∧
        (∀ u d, u < d → ∃ k : ℕ,
          c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d) ∧
        (∀ d,
          ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
            (S.core.parameters.M N : ℤ)) := by
    filter_upwards [S.core.chain_coefficients,
      S.gapStage.coefficient_divides_modulus] with N hchain hdiv
    obtain ⟨c, hc, hpos, hratio⟩ := hchain m C a ha
    refine ⟨c, ?_, hpos, hratio, ?_⟩
    · simpa [chainScale] using hc
    · intro d
      exact hdiv m C a ha c hc d
  have hmassRatio : Tendsto
      (fun N => primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper /
          (masterScaleV S.core.parameters N C.gap : ℝ)) atTop atTop := by
    simpa [pow_one] using S.primeStage.pool_harmonic_mass_dominates C.gap 1 (by norm_num)
  have hmassEvent : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper := by
    filter_upwards [hmassRatio.eventually_ge_atTop (1 : ℝ)] with N hN
    have hV : 0 < (masterScaleV S.core.parameters N C.gap : ℝ) := by
      unfold masterScaleV
      positivity
    have hmul : (masterScaleV S.core.parameters N C.gap : ℝ) ≤
        primePoolMass (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper := by
      simpa using (le_div_iff₀ hV).mp hN
    have hmass : (0 : ℝ) <
        primePoolMass (S.primeStage.pool N C.gap).lower
          (S.primeStage.pool N C.gap).upper := lt_of_lt_of_le hV hmul
    exact hmass
  have hlowerRatio : Tendsto
      (fun N => ((S.primeStage.pool N C.gap).lower : ℝ) /
        (masterScaleV S.core.parameters N C.gap : ℝ)) atTop atTop := by
    simpa [pow_one] using S.primeStage.pool_lower_dominates C.gap 1 (by norm_num)
  have hlowerEvent : ∀ᶠ N in atTop,
      masterScaleV S.core.parameters N C.gap + 1 <
        (S.primeStage.pool N C.gap).lower := by
    filter_upwards [hlowerRatio.eventually_ge_atTop (2 : ℝ)] with N hN
    have hVnat : 2 ≤ masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      omega
    have hV : 0 < (masterScaleV S.core.parameters N C.gap : ℝ) := by positivity
    have hmul : 2 * (masterScaleV S.core.parameters N C.gap : ℝ) ≤
        (S.primeStage.pool N C.gap).lower := (le_div_iff₀ hV).mp hN
    have hmulNat : 2 * masterScaleV S.core.parameters N C.gap ≤
        (S.primeStage.pool N C.gap).lower := by exact_mod_cast hmul
    omega
  let T : ℕ → ℕ := fun N => (S.primeStage.pool N C.gap).upper +
    masterScaleV S.core.parameters N C.gap
  have hT : ∀ N, 1 ≤ T N := by
    intro N
    dsimp [T]
    have hV : 2 ≤ masterScaleV S.core.parameters N C.gap := by
      unfold masterScaleV
      omega
    omega
  have hDmin := nat_div_lower_from_dominance
    (Filter.Eventually.of_forall hT)
    (by simpa [T] using S.gapStage.gap_dominates_pool_and_bound C.gap)
    J0 B 1 hJ0
  have hDminEvent : ∀ᶠ N in atTop,
      1 ≤ S.core.parameters.H N C.gap / (J0 * T N ^ B) := by
    filter_upwards [hDmin] with N hN
    have hT2 : 2 ≤ T N := by
      dsimp [T]
      have hV : 2 ≤ masterScaleV S.core.parameters N C.gap := by
        unfold masterScaleV
        omega
      omega
    have hN' : T N ≤ S.core.parameters.H N C.gap / (J0 * T N ^ B) := by
      simpa [pow_one] using hN
    exact le_trans (by omega) hN'
  filter_upwards [hcoeff, hfactsEvent, hmassEvent, hlowerEvent, hDminEvent]
    with N hcoeffN hfactsN hmassN hlowerN hDminN
  refine ⟨hcoeffN, hfactsN, hmassN, hlowerN, ?_⟩
  simpa [T] using hDminN

theorem pkgElim_responseUnit_integer {N V q : ℕ}
    {tests : Finset (IntegerPolynomial q)} {p : Fin q → ℕ} {x : ℚ}
    (h : ResponseUnit N V tests p x) : ∃ z : ℤ, x = (z : ℚ) := by
  refine ⟨x.num, ?_⟩
  exact (Rat.den_eq_one_iff x).mp h.2.1 |>.symm

theorem pkgElim_rationalResidue_intCast {r : ℕ} (hr : r.Prime) (z : ℤ) :
    FromArithmetic.rationalResidue r hr (z : ℚ) = (z : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  simp [FromArithmetic.rationalResidue]

theorem pkgElim_occurrenceAnchor_residue_ne_zero {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (N : ℕ) (p : Fin q → ℕ) (o : Occurrence Sh) (J0 B : ℕ)
    (hGlobal : pkgElim_momentGlobalData S C a Sh dirs tests J0 B N)
    (hGood : GoodTuple S C.gap N tests dirs.poly p)
    (π : ℕ) (hπ : π.Prime) (hπN : N + 1 < π)
    (hπV : π ≤ masterScaleV S.core.parameters N C.gap) :
    FromArithmetic.rationalResidue π hπ
      (occurrenceCoeff S C a Sh dirs N p o
        (.inl (Sh.row (occurrenceRow Sh o)).anchor)) ≠ 0 := by
  classical
  letI : Fact π.Prime := ⟨hπ⟩
  rcases hGlobal with ⟨⟨c, hcVal, hcPos, hcRatio, hcDiv⟩, hFacts, hMass, hLower, hLength⟩
  let T := Sh.row (occurrenceRow Sh o)
  have hanchorMem : T.anchor ∈ T.support := Finset.max'_mem T.support T.support_nonempty
  have hentrySome : (T.entry T.anchor).isSome := by
    simpa [RowTemplate.support] using hanchorMem
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hentrySome
  have hscale : chainScale S.core.parameters C a N T.anchor = (c T.anchor : ℚ) :=
    (hcVal T.anchor).symm
  have hcposQ : 0 < (c T.anchor : ℚ) := by exact_mod_cast hcPos T.anchor
  have hcne : chainScale S.core.parameters C a N T.anchor ≠ 0 := by
    rw [hscale]
    exact ne_of_gt hcposQ
  have hcoeff : occurrenceCoeff S C a Sh dirs N p o (.inl T.anchor) = T.value p T.anchor := by
    change rowTemplateCoefficient (chainScale S.core.parameters C a N) T p T.anchor = _
    unfold rowTemplateCoefficient
    rw [div_self hcne, one_mul]
  have hval : T.value p T.anchor =
      ((∏ i : Fin q, (p i : ℤ) ^ e i : ℤ) : ℚ) := by
    simp [RowTemplate.value, T, he]
  have hpiNZ : ∀ i : Fin q, (p i : ZMod π) ≠ 0 := by
    intro i hz
    have hdvd : π ∣ p i := (ZMod.natCast_eq_zero_iff (p i) π).mp hz
    have hprime := (hGood.1 i).2.2
    have hlt : π < p i := by
      have hpool : (S.primeStage.pool N C.gap).lower ≤ p i := (hGood.1 i).1
      have hbound : masterScaleV S.core.parameters N C.gap + 1 <
          (S.primeStage.pool N C.gap).lower := hLower
      omega
    have heq : π = p i := (Nat.prime_dvd_prime_iff_eq hπ hprime).mp hdvd
    omega
  have hprodNZ : (∏ i : Fin q, (p i : ZMod π) ^ e i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hpiNZ i)
  rw [hcoeff, hval, pkgElim_rationalResidue_intCast]
  simpa using hprodNZ

theorem pkgElim_occurrenceCoeff_integer {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (N : ℕ) (p : Fin q → ℕ) (o : Occurrence Sh) (v : Coordinate Sh)
    (J0 B : ℕ) (hGlobal : pkgElim_momentGlobalData S C a Sh dirs tests J0 B N)
    (hGood : GoodTuple S C.gap N tests dirs.poly p) :
    ∃ z : ℤ, occurrenceCoeff S C a Sh dirs N p o v = (z : ℚ) := by
  classical
  rcases hGlobal with ⟨⟨c, hcVal, hcPos, hcRatio, hcDiv⟩, hFacts, hMass, hLower, hLength⟩
  have hscale : ∀ d, chainScale S.core.parameters C a N d = (c d : ℚ) := by
    intro d
    exact (hcVal d).symm
  have hfacts := hFacts p hGood
  cases o with
  | inl ω =>
    cases v with
    | inl k =>
      obtain ⟨z, hz⟩ := pkgElim_rowTemplateCoefficient_integer
        (T := Sh.row Sh.star) p k (chainScale S.core.parameters C a N) c
        hscale hcPos (primorial (N + 1)) hcRatio
      exact ⟨z, by simpa [occurrenceCoeff, occurrenceRow] using hz⟩
    | inr v =>
      cases v with
      | inl re =>
        rcases re with ⟨R, e⟩
        by_cases he : e = ω R
        · refine ⟨(directionModulus S N dirs.poly p : ℤ), ?_⟩
          simp [occurrenceCoeff, he]
        · exact ⟨0, by simp [occurrenceCoeff, he]⟩
      | inr j => exact ⟨0, by simp [occurrenceCoeff]⟩
  | inr pair =>
    rcases pair with ⟨j, ⟨I, η⟩⟩
    cases v with
    | inl k =>
      obtain ⟨z, hz⟩ := pkgElim_rowTemplateCoefficient_integer
        (T := Sh.row I.1) p k (chainScale S.core.parameters C a N) c
        hscale hcPos (primorial (N + 1)) hcRatio
      exact ⟨z, by simpa [occurrenceCoeff, occurrenceRow] using hz⟩
    | inr v =>
      cases v with
      | inl re =>
        rcases re with ⟨R, e⟩
        by_cases hRI : R ≠ I
        · by_cases he : e = η ⟨R, hRI⟩
          · rcases hfacts with ⟨_, _, _, _, _, _, hResponse, _⟩
            have hIR : I.1 ≠ R.1 := by
              intro hval
              apply hRI
              exact Subtype.ext hval.symm
            obtain ⟨z, hz⟩ := pkgElim_responseUnit_integer
              (hResponse R.1 I.1 R.property hIR)
            exact ⟨z, by simpa [occurrenceCoeff, occurrenceRow, hRI, he] using hz⟩
          · exact ⟨0, by simp [occurrenceCoeff, hRI, he]⟩
        · exact ⟨0, by simp [occurrenceCoeff, hRI]⟩
      | inr j' =>
        by_cases hj : j' = j
        · rcases hfacts with ⟨_, _, _, _, _, _, _, hRootResponse⟩
          obtain ⟨z, hz⟩ := pkgElim_responseUnit_integer
            (hRootResponse I.1 I.property)
          exact ⟨z, by simpa [occurrenceCoeff, occurrenceRow, hj] using hz⟩
        · exact ⟨0, by simp [occurrenceCoeff, hj]⟩

theorem pkgElim_linearRowValue_integer {K m q r s h d : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (eO : Occurrence Sh ≃ Fin h)
    (eX : Coordinate Sh ≃ Fin d) (N : ℕ) (p' : Fin s → ℕ)
    (u : Fin h) (x : Fin d → ℤ) (J0 B : ℕ)
    (tests : Finset (IntegerPolynomial q))
    (hGlobal : pkgElim_momentGlobalData S C a Sh dirs tests J0 B N)
    (hGood : GoodTuple S C.gap N tests dirs.poly (fun i => p' (ι i))) :
    ∃ z : ℤ,
      FromArithmetic.linearRowValue (rowCoeff S ι C a Sh dirs eO eX)
        N p' u x = (z : ℚ) := by
  classical
  have hcoeff : ∀ j : Fin d, ∃ z : ℤ,
      occurrenceCoeff S C a Sh dirs N (fun i => p' (ι i))
        (eO.symm u) (eX.symm j) = (z : ℚ) := by
    intro j
    exact pkgElim_occurrenceCoeff_integer S C a Sh dirs tests N
      (fun i => p' (ι i)) (eO.symm u) (eX.symm j) J0 B hGlobal hGood
  choose z hz using hcoeff
  refine ⟨∑ j : Fin d, z j * x j, ?_⟩
  unfold FromArithmetic.linearRowValue rowCoeff
  calc
    _ = ∑ j : Fin d, ((z j * x j : ℤ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hz j]
      simp
    _ = ((∑ j : Fin d, z j * x j : ℤ) : ℚ) := by simp

noncomputable def pkgElim_momentOldResidueError {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (J0 B N : ℕ) : ℝ :=
  let V := masterScaleV S.core.parameters N C.gap
  let T := (S.primeStage.pool N C.gap).upper + V
  let Dmin := S.core.parameters.H N C.gap / (J0 * T ^ B)
  2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) / (Dmin : ℝ)

noncomputable def pkgElim_momentRootResidueError {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (N : ℕ) : ℝ :=
  2 * (masterScaleV S.core.parameters N C.gap : ℝ) ^ Fintype.card (Occurrence Sh) /
    (S.core.parameters.H N C.gap : ℝ)

noncomputable def pkgElim_momentBaseError {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (Sh : RowShape m q r) (J0 B N : ℕ) : ℝ :=
  (∑ k : Fin m, FromArithmetic.harmonicResidueUniformError
      (S.core.parameters.X N (C.block k).1) (primorial (N + 1))
      (masterScaleV S.core.parameters N C.gap ^ Fintype.card (Occurrence Sh))) +
    ((2 * Fintype.card (NonTarget Sh) : ℕ) : ℝ) *
      pkgElim_momentOldResidueError S C Sh J0 B N +
    2 * pkgElim_momentRootResidueError S C Sh N

noncomputable def pkgElim_momentCRTError {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 B N : ℕ) : ℝ := by
  classical
  let V := masterScaleV S.core.parameters N C.gap
  let lo := (S.primeStage.pool N C.gap).lower
  let hi := (S.primeStage.pool N C.gap).upper
  let e := S.primeStage.e0 N
  let δ := finiteL1 (primePoolResidueLaw lo hi
      (FromArithmetic.masterCRTModulus (N + 1) e V))
    (uniformUnitResidueLaw (FromArithmetic.masterCRTModulus (N + 1) e V))
  exact if pkgElim_momentGlobalData S C a Sh dirs tests J0 B N then
      (s : ℝ) * δ
    else finiteL1
      (FromArithmetic.primeTupleCRTLaw (fun _ : Fin s => lo) (fun _ => hi) (N + 1) V)
      (FromArithmetic.uniformPrimeTupleCRTLaw (N + 1) V)

theorem pkgElim_harmonicResidueError_mono {X W k K : ℕ}
    (hk : k ≤ K) (hW : 0 < W) (hX : 4 * W ≤ X) :
    FromArithmetic.harmonicResidueUniformError X W k ≤
      FromArithmetic.harmonicResidueUniformError X W K := by
  have hXpos : 0 < (X : ℝ) := by
    have hWpos : 0 < primorial (0 + 1) := by norm_num
    have : 0 < W := hW
    have hXnat : 0 < X := by omega
    exact_mod_cast hXnat
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast hW
  have hden : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X) := by
    apply mul_pos hXpos
    exact sub_pos.mpr (harmonic_cutoff_log_condition hW hX)
  have hkcast : ((k + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hk 1
  have hnum : (W : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
      (W : ℝ) * ((K + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hkcast hWpos.le
  unfold FromArithmetic.harmonicResidueUniformError FromArithmetic.harmonicResidueError
  exact div_le_div_of_nonneg_right hnum hden.le

theorem pkgElim_coordinateResidueTV {K m q r s : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 B N : ℕ) (hJ0 : 0 < J0)
    (p : Fin q → ℕ) (v : Coordinate Sh) (Kdiv : ℕ) (hKdiv : 0 < Kdiv)
    (hKcop : Nat.Coprime Kdiv (primorial (N + 1)))
    (hKle : Kdiv ≤
      masterScaleV S.core.parameters N C.gap ^ Fintype.card (Occurrence Sh))
    (hGlobal : pkgElim_momentGlobalData S C a Sh dirs tests J0 B N)
    (hGood : GoodTuple S C.gap N tests dirs.poly p) :
    finiteL1 (integerResidueLaw Kdiv hKdiv
      (coordinateLaw S C Sh dirs J0 N p v)) (uniformResidueLaw Kdiv) ≤
    match v with
    | .inl k => FromArithmetic.harmonicResidueUniformError
        (S.core.parameters.X N (C.block k).1) (primorial (N + 1))
        (masterScaleV S.core.parameters N C.gap ^ Fintype.card (Occurrence Sh))
    | .inr (.inl _) => pkgElim_momentOldResidueError S C Sh J0 B N
    | .inr (.inr _) => pkgElim_momentRootResidueError S C Sh N := by
  classical
  cases v with
  | inl k =>
    have hW : 0 < primorial (N + 1) := primorial_pos _
    have hX := S.gapStage.valid_raw_cutoffs N (C.block k).1
    have hX2 : 2 ≤ S.core.parameters.X N (C.block k).1 := by
      have hWpos : 0 < primorial (N + 1) := primorial_pos _
      omega
    have hlog := harmonic_cutoff_log_condition hW hX
    have htv := harmonicIntegerResidueLaw_tv hW hX2 hlog hKcop hKdiv
    have hmono := pkgElim_harmonicResidueError_mono hKle hW hX
    change finiteL1 (integerResidueLaw Kdiv hKdiv
      (harmonicLaw (S.core.parameters.X N (C.block k).1) (primorial (N + 1))))
      (uniformResidueLaw Kdiv) ≤
      FromArithmetic.harmonicResidueUniformError
        (S.core.parameters.X N (C.block k).1) (primorial (N + 1))
        (masterScaleV S.core.parameters N C.gap ^ Fintype.card (Occurrence Sh))
    exact htv.trans hmono
  | inr v =>
    cases v with
    | inl old =>
      rcases hGlobal with ⟨_, hFacts, _, _, hDmin⟩
      let V := masterScaleV S.core.parameters N C.gap
      let T := (S.primeStage.pool N C.gap).upper + V
      let Dmin := S.core.parameters.H N C.gap / (J0 * T ^ B)
      let L := shiftLength S C.gap J0 N dirs.poly p
      let Lmax := max 1 L
      have hDmin1 : 1 ≤ Dmin := by simpa [Dmin, T, V] using hDmin
      rcases hFacts p hGood with ⟨_, _, hMpBound, _, _, _, _, _⟩
      have hMpPos : 0 < directionModulus S N dirs.poly p := by
        unfold directionModulus
        exact Nat.mul_pos (S.core.parameters.Mpos N) (roughPart_pos _ _)
      have hdenLe : J0 * directionModulus S N dirs.poly p ≤ J0 * T ^ B := by
        dsimp [T, V]
        exact Nat.mul_le_mul_left J0 hMpBound
      have hdenPos : 0 < J0 * directionModulus S N dirs.poly p :=
        Nat.mul_pos hJ0 hMpPos
      have hDminLeL : Dmin ≤ L := by
        dsimp [Dmin, L]
        exact Nat.div_le_div_left hdenLe hdenPos
      have hLone : 1 ≤ L := le_trans hDmin1 hDminLeL
      have hLmax : Lmax = L := max_eq_right hLone
      have hLpos : 0 < Lmax := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
      have htv := uniformIntegerInterval_residue_tv hKdiv hLpos
      have hKleR : (Kdiv : ℝ) ≤ (V : ℝ) ^ Fintype.card (Occurrence Sh) := by
        exact_mod_cast hKle
      have hnum : 2 * (Kdiv : ℝ) ≤ 2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) :=
        mul_le_mul_of_nonneg_left hKleR (by norm_num)
      have hDminPos : 0 < (Dmin : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDmin1)
      have hDminLeL : (Dmin : ℝ) ≤ (Lmax : ℝ) := by
        rw [hLmax]
        exact_mod_cast hDminLeL
      have hTV1 : 2 * (Kdiv : ℝ) / (Lmax : ℝ) ≤
          2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) / (Lmax : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      have hTV2 : 2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) / (Lmax : ℝ) ≤
          2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) / (Dmin : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hDminPos hDminLeL
      have hbound : 2 * (Kdiv : ℝ) / (Lmax : ℝ) ≤
          pkgElim_momentOldResidueError S C Sh J0 B N := by
        calc
          _ ≤ 2 * (V : ℝ) ^ Fintype.card (Occurrence Sh) / (Dmin : ℝ) := hTV1.trans hTV2
          _ = pkgElim_momentOldResidueError S C Sh J0 B N := by
            simp [pkgElim_momentOldResidueError, V, T, Dmin]
      change finiteL1 (integerResidueLaw Kdiv hKdiv
        (FromArithmetic.uniformIntegerIntervalLaw 0 (max 1 (shiftLength S C.gap J0 N dirs.poly p))))
        (uniformResidueLaw Kdiv) ≤ pkgElim_momentOldResidueError S C Sh J0 B N
      simpa [Lmax, L, hLmax] using htv.trans hbound
    | inr root =>
      have hH : 0 < S.core.parameters.H N C.gap := S.core.parameters.Hpos N C.gap
      have htv := uniformIntegerInterval_residue_tv hKdiv hH
      have hKleR : (Kdiv : ℝ) ≤
          (masterScaleV S.core.parameters N C.gap : ℝ) ^ Fintype.card (Occurrence Sh) := by
        exact_mod_cast hKle
      have hnum : 2 * (Kdiv : ℝ) ≤
          2 * (masterScaleV S.core.parameters N C.gap : ℝ) ^ Fintype.card (Occurrence Sh) :=
        mul_le_mul_of_nonneg_left hKleR (by norm_num)
      have hHpos : 0 < (S.core.parameters.H N C.gap : ℝ) := by exact_mod_cast hH
      have hbound : 2 * (Kdiv : ℝ) / (S.core.parameters.H N C.gap : ℝ) ≤
          pkgElim_momentRootResidueError S C Sh N := by
        simpa [pkgElim_momentRootResidueError] using
          div_le_div_of_nonneg_right hnum hHpos.le
      change finiteL1 (integerResidueLaw Kdiv hKdiv
        (FromArithmetic.uniformIntegerIntervalLaw 0 (S.core.parameters.H N C.gap)))
        (uniformResidueLaw Kdiv) ≤ pkgElim_momentRootResidueError S C Sh N
      simpa [pkgElim_momentRootResidueError] using htv.trans hbound

theorem pkgElim_momentBaseResidueUniform {K m q r s d h : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : MasterScales K Aset s Dm) (ι : Fin q ↪ Fin s)
    (C : MasterChain K m) (a : Fin m → ℚ)
    (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (J0 B N : ℕ) (hJ0 : 0 < J0)
    (eO : Occurrence Sh ≃ Fin h) (eX : Coordinate Sh ≃ Fin d)
    (F : Finset (Occurrence Sh)) (p' : Fin s → ℕ)
    (hGlobal : pkgElim_momentGlobalData S C a Sh dirs tests J0 B N)
    (hGood : GoodTuple S C.gap N tests dirs.poly (fun i => p' (ι i)))
    (σ : Fin h → ℕ)
    (hσ : ∀ u, FromArithmetic.divisorTemplateLaw S.core.parameters N
      (pkgElim_momentDivisorTemplate C Sh eO F u) (σ u) ≠ 0) :
    finiteL1
      (FromArithmetic.baseResidueLaw
        (∏ u : Fin h, σ u) (by
          apply Finset.prod_pos
          intro u hu
          exact Nat.lt_of_lt_of_le Nat.zero_lt_one
            ((pkgElim_momentDivisorTemplate_support S C Sh eO F N u (σ u) (hσ u)).1))
        (fun x => coordinateProductLaw S C Sh dirs J0 N
          (fun i => p' (ι i)) eX x))
      (FromArithmetic.uniformBaseResidueLaw (∏ u : Fin h, σ u) d) ≤
      pkgElim_momentBaseError S C Sh J0 B N := by
  classical
  let Kdiv : ℕ := ∏ u : Fin h, σ u
  have hσFacts (u : Fin h) :=
    pkgElim_momentDivisorTemplate_support S C Sh eO F N u (σ u) (hσ u)
  have hKdivPos : 0 < Kdiv := by
    dsimp [Kdiv]
    apply Finset.prod_pos
    intro u hu
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hσFacts u).1
  have hKdivCop : Nat.Coprime Kdiv (primorial (N + 1)) := by
    dsimp [Kdiv]
    rw [Nat.coprime_prod_left_iff]
    intro u hu
    exact (hσFacts u).2.2
  have hKdivLe : Kdiv ≤ masterScaleV S.core.parameters N C.gap ^ h := by
    dsimp [Kdiv]
    calc
      _ ≤ ∏ u : Fin h, masterScaleV S.core.parameters N C.gap := by
        apply Finset.prod_le_prod
        intro u hu
        exact (hσFacts u).2.1
      _ = masterScaleV S.core.parameters N C.gap ^ h := by simp
  let μ : Fin d → ℤ → ℝ := fun i =>
    coordinateLaw S C Sh dirs J0 N (fun j => p' (ι j)) (eX.symm i)
  let supp : Fin d → Finset ℤ := fun i =>
    pkgElim_coordinateSupport S C Sh dirs J0 N (fun j => p' (ι j)) (eX.symm i)
  let errV : Coordinate Sh → ℝ := fun v => match v with
    | .inl k => FromArithmetic.harmonicResidueUniformError
        (S.core.parameters.X N (C.block k).1) (primorial (N + 1))
        (masterScaleV S.core.parameters N C.gap ^ h)
    | .inr (.inl _) => pkgElim_momentOldResidueError S C Sh J0 B N
    | .inr (.inr _) => pkgElim_momentRootResidueError S C Sh N
  let ε : Fin d → ℝ := fun i => errV (eX.symm i)
  have hCard : Fintype.card (Occurrence Sh) = h := by
    simpa using Fintype.card_congr eO
  have hsupp : ∀ i z, z ∉ supp i → μ i z = 0 := by
    intro i z hz
    exact pkgElim_coordinateLaw_zero_of_not_mem S C Sh dirs J0 N
      (fun j => p' (ι j)) (eX.symm i) z hz
  have hnorm (i : Fin d) : ∑' z : ℤ, μ i z = 1 :=
    pkgElim_coordinateLaw_tsum_one S C Sh dirs J0 N
      (fun j => p' (ι j)) (eX.symm i)
  have hcoordNonneg : ∀ i x, 0 ≤ integerResidueLaw Kdiv hKdivPos (μ i) x := by
    intro i x
    exact integerResidueLaw_nonneg hKdivPos (μ i) (supp i) (hsupp i)
      (fun z => pkgElim_coordinateLaw_nonneg S C Sh dirs J0 N
        (fun j => p' (ι j)) (eX.symm i) z) x
  have hcoordNorm : ∀ i, ∑ x : Fin Kdiv, integerResidueLaw Kdiv hKdivPos (μ i) x = 1 := by
    intro i
    exact integerResidueLaw_sum_one hKdivPos (μ i) (supp i) (hsupp i) (hnorm i)
  have hcoordTV : ∀ i : Fin d,
      finiteL1 (integerResidueLaw Kdiv hKdivPos (μ i)) (uniformResidueLaw Kdiv) ≤ ε i := by
    intro i
    have hKdivLe' : Kdiv ≤ masterScaleV S.core.parameters N C.gap ^
        Fintype.card (Occurrence Sh) := by
      rw [hCard]
      exact hKdivLe
    have h := pkgElim_coordinateResidueTV S C a Sh dirs tests J0 B N hJ0
      (fun j => p' (ι j)) (eX.symm i) Kdiv hKdivPos hKdivCop hKdivLe'
      hGlobal hGood
    simpa [ε, errV, hCard] using h
  let r : Fin d → Fin Kdiv := fun _ => ⟨0, hKdivPos⟩
  have hprodTV := productBaseResidueLaw_finiteL1_le hKdivPos μ supp hsupp r
    hcoordNonneg hcoordNorm ε hcoordTV
  have hsumReindex :
      (∑ i : Fin d, ε i) = ∑ v : Coordinate Sh, errV v := by
    exact (Fintype.sum_equiv eX (fun v => errV v)
      (fun i => errV (eX.symm i)) (by intro v; simp)).symm
  have hsumError : (∑ i : Fin d, ε i) =
      pkgElim_momentBaseError S C Sh J0 B N := by
    rw [hsumReindex]
    simp [errV, pkgElim_momentBaseError, pkgElim_momentOldResidueError,
      pkgElim_momentRootResidueError, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Finset.sum_const, nsmul_eq_mul, hCard]
    ring
  calc
    finiteL1
        (FromArithmetic.baseResidueLaw Kdiv hKdivPos
          (fun x => coordinateProductLaw S C Sh dirs J0 N
            (fun i => p' (ι i)) eX x))
        (FromArithmetic.uniformBaseResidueLaw Kdiv d) =
      finiteL1
        (FromArithmetic.baseResidueLaw Kdiv hKdivPos (fun x => ∏ i, μ i (x i)))
        (FromArithmetic.uniformBaseResidueLaw Kdiv d) := by
          congr 1
    _ ≤ ∑ i : Fin d, ε i := hprodTV
    _ = pkgElim_momentBaseError S C Sh J0 B N := hsumError

end AdditiveMoment

end HindmanSumsProducts
