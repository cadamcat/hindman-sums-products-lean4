import HindmanSumsProducts.Prediction.Results

/-! Helper lemmas for §5 (part S5-E). -/

namespace HindmanSumsProducts.Prediction

open scoped BigOperators NNReal Topology BoundedContinuousFunction
open Filter
open OAI.SourceMenuLiteral

variable {K : ℕ}

/-- Reindex a representing family from a larger gap interval to a divisor interval. -/
theorem RepFamily.reindex_of_dvd {A : Parameters K} {l l' : Fin K}
    {s : ℕ} {Fm : Menu s} {Km : ℝ≥0}
    (Φ : RepFamily A l' Fm Km) (hdiv : ∀ N, A.H N l ∣ A.H N l') :
    ∃ Ψ : RepFamily A l Fm Km, ∀ N y, Ψ.eval N y = Φ.eval N y := by
  let Ψ : RepFamily A l Fm Km := {
    piece := fun N q r => Φ.piece N
      (q / ((A.H N l' / A.H N l : ℕ) : ℤ)) r }
  refine ⟨Ψ, ?_⟩
  intro N y
  have hmulN : A.H N l * (A.H N l' / A.H N l) = A.H N l' :=
    Nat.mul_div_cancel' (hdiv N)
  have hq : y / (A.H N l : ℤ) / ((A.H N l' / A.H N l : ℕ) : ℤ) =
      y / (A.H N l' : ℤ) := by
    rw [Int.ediv_ediv_of_nonneg (Int.natCast_nonneg (A.H N l))]
    congr 1
    exact_mod_cast hmulN
  simp only [RepFamily.eval, Ψ]
  rw [hq]

/-- Raise every piece in a representing family along `raiseMenu`. -/
def RepFamily.raise {A : Parameters K} {l : Fin K} {s s' : ℕ}
    {Fm : Menu s} {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (h : s ≤ s') :
    RepFamily A l (raiseMenu Fm h) Km := {
      piece := fun N q r => (Φ.piece N q r).raise h }

@[simp] theorem RepFamily.raise_eval {A : Parameters K} {l : Fin K} {s s' : ℕ}
    {Fm : Menu s} {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (h : s ≤ s')
    (N : ℕ) (y : ℤ) : (Φ.raise h).eval N y = Φ.eval N y := by
  dsimp [RepFamily.eval, RepFamily.raise, OAI.SourceMenuLiteral.CosetPiece.raise,
    OAI.SourceMenuLiteral.raiseMenu, OAI.SourceMenuLiteral.CosetPiece.eval]

/-- Compose a representing piece with a Lipschitz map into the unit interval. -/
def CosetPiece.comp01 {s : ℕ} {Fm : Menu s} {Km : ℝ≥0}
    (P : CosetPiece Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) :
    CosetPiece Fm (L * Km) := by
  let obs : (Fm.G P.index ⧸ Fm.Γ P.index) →ᵇ ℝ := {
    toContinuousMap := ⟨ψ ∘ P.obs, hψ.continuous.comp P.obs.continuous⟩
    map_bounded' := ⟨1, fun z w => by
      rw [Real.dist_eq]
      have hz := hψ01 (P.obs z) (P.range z)
      have hw := hψ01 (P.obs w) (P.range w)
      have hz' : 0 ≤ ψ (P.obs z) ∧ ψ (P.obs z) ≤ 1 := by simpa using hz
      have hw' : 0 ≤ ψ (P.obs w) ∧ ψ (P.obs w) ≤ 1 := by simpa using hw
      change |ψ (P.obs z) - ψ (P.obs w)| ≤ 1
      rw [abs_le]
      constructor
      · linarith [hz'.1, hw'.2]
      · linarith [hz'.2, hw'.1]⟩ }
  exact {
    index := P.index
    g := P.g
    x := P.x
    obs := obs
    lip := by
      letI : MetricSpace (Fm.G P.index ⧸ Fm.Γ P.index) :=
        (Fm.metric P.index).replaceTopology (Fm.compatible P.index)
      change LipschitzWith (L * Km) (fun z => ψ (P.obs z))
      exact hψ.comp P.lip
    range := fun z => hψ01 (P.obs z) (P.range z) }

@[simp] theorem CosetPiece.comp01_eval {s : ℕ} {Fm : Menu s} {Km : ℝ≥0}
    (P : CosetPiece Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) (m : ℤ) :
    (P.comp01 ψ L hψ hψ01).eval m = ψ (P.eval m) := by
  change (P.comp01 ψ L hψ hψ01).obs (P.g ^ m • P.x) =
    ψ (P.obs (P.g ^ m • P.x))
  dsimp [CosetPiece.comp01]
  rfl

/-- Pointwise composition of an entire representing family. -/
theorem RepFamily.compMap {A : Parameters K} {l : Fin K} {s : ℕ} {Fm : Menu s}
    {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0)
    (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Ψ : RepFamily A l Fm (L * Km),
      ∀ N y, Ψ.eval N y = ψ (Φ.eval N y) := by
  let Ψ : RepFamily A l Fm (L * Km) := {
    piece := fun N q r => (Φ.piece N q r).comp01 ψ L hψ hψ01 }
  refine ⟨Ψ, ?_⟩
  intro N y
  simp [RepFamily.eval, Ψ]

/-- The finite support of the harmonic law, expressed as signed integers. -/
def muSupport (A : Parameters K) (N : ℕ) (i : Fin K) : Finset ℤ :=
  Finset.image (fun n : ℕ => (n : ℤ))
    ((Finset.Ico (A.X N i) ((A.X N i) ^ 2)).filter
      (fun n => Nat.Coprime n (primorial (N + 1))))

private theorem mu_zero_of_not_mem (A : Parameters K) (N : ℕ) (i : Fin K) (y : ℤ)
    (hy : y ∉ muSupport A N i) : mu A N i y = 0 := by
  unfold mu harmonicLaw
  split_ifs with h
  · exfalso
    apply hy
    unfold muSupport
    apply Finset.mem_image.mpr
    refine ⟨y.toNat, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩,
      h.2.2.2⟩, Int.toNat_of_nonneg h.1⟩
  · rfl

theorem Emu_eq_sum_support (A : Parameters K) (N : ℕ) (i : Fin K)
    (f : ℤ → ℝ) :
    Emu A N i f = ∑ y ∈ muSupport A N i, mu A N i y * f y := by
  classical
  unfold Emu
  exact tsum_eq_sum (s := muSupport A N i) (fun y hy => by
    simp [mu_zero_of_not_mem A N i y hy])

theorem mu_nonneg (A : Parameters K) (N : ℕ) (i : Fin K) (y : ℤ) :
    0 ≤ mu A N i y := by
  have hnorm : 0 ≤ harmonicNormalizer (A.X N i) (primorial (N + 1)) := by
    unfold harmonicNormalizer
    apply Finset.sum_nonneg
    intro n hn
    exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  unfold mu harmonicLaw
  split_ifs with h
  · exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hnorm)
  · exact le_rfl

theorem Emu_nonneg (A : Parameters K) (N : ℕ) (i : Fin K)
    (f : ℤ → ℝ) (hf : ∀ y, 0 ≤ f y) : 0 ≤ Emu A N i f := by
  rw [Emu_eq_sum_support]
  apply Finset.sum_nonneg
  intro y hy
  exact mul_nonneg (mu_nonneg A N i y) (hf y)

theorem Emu_mass_le_one (A : Parameters K) (N : ℕ) (i : Fin K) :
    Emu A N i (fun _ => 1) ≤ 1 := by
  classical
  let T := (Finset.Ico (A.X N i) ((A.X N i) ^ 2)).filter
    (fun n => Nat.Coprime n (primorial (N + 1)))
  let H := harmonicNormalizer (A.X N i) (primorial (N + 1))
  rw [Emu_eq_sum_support]
  change (∑ y ∈ Finset.image (fun n : ℕ => (n : ℤ)) T, mu A N i y * 1) ≤ 1
  rw [Finset.sum_image Nat.cast_injective.injOn]
  calc
    (∑ n ∈ T, mu A N i (n : ℤ) * 1) =
        ∑ n ∈ T, 1 / ((n : ℝ) * H) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hmem := Finset.mem_filter.mp hn
      have hIco := Finset.mem_Ico.mp hmem.1
      have hvalid : 0 ≤ (n : ℤ) ∧ A.X N i ≤ Int.toNat (n : ℤ) ∧
          Int.toNat (n : ℤ) < (A.X N i) ^ 2 ∧
          Nat.Coprime (Int.toNat (n : ℤ)) (primorial (N + 1)) := by
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · simpa only [Int.toNat_natCast] using hIco.1
        · simpa only [Int.toNat_natCast] using hIco.2
        · simpa only [Int.toNat_natCast] using hmem.2
      simp only [mu, harmonicLaw]
      rw [if_pos hvalid]
      simp [H, Int.toNat_natCast]
    _ = ∑ n ∈ T, (1 / (n : ℝ)) / H := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        1 / ((n : ℝ) * H) = (n : ℝ)⁻¹ * H⁻¹ := by
          rw [one_div, mul_inv_rev]
          ring
        _ = (1 / (n : ℝ)) / H := by
          simp [one_div, div_eq_mul_inv, mul_comm]
    _ = (∑ n ∈ T, 1 / (n : ℝ)) / H := by rw [Finset.sum_div]
    _ = H / H := by simp [H, T, harmonicNormalizer]
    _ ≤ 1 := by
      by_cases hH : H = 0 <;> simp [hH]

theorem Emu_abs_inner_le (A : Parameters K) (N : ℕ) (i : Fin K)
    (f g : ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ y, |f y| ≤ C) :
    |Emu A N i (fun y => f y * g y)| ≤
      (C ^ 2 * Emu A N i (fun _ => 1) +
        Emu A N i (fun y => g y * g y)) / 2 := by
  classical
  rw [Emu_eq_sum_support, Emu_eq_sum_support, Emu_eq_sum_support]
  calc
    |∑ y ∈ muSupport A N i, mu A N i y * (f y * g y)| ≤
        ∑ y ∈ muSupport A N i, |mu A N i y * (f y * g y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ muSupport A N i,
        mu A N i y * ((C ^ 2 + g y * g y) / 2) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul, abs_of_nonneg (mu_nonneg A N i y)]
      have hsq : f y * f y ≤ C ^ 2 := by
        have habs := abs_le.mp (hf y)
        nlinarith
      have hprod : |f y * g y| ≤ (f y * f y + g y * g y) / 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f y - g y), sq_nonneg (f y + g y)]
      have hprod' : |f y * g y| ≤ (C ^ 2 + g y * g y) / 2 := by
        nlinarith [hprod, hsq]
      exact mul_le_mul_of_nonneg_left hprod' (mu_nonneg A N i y)
    _ = (C ^ 2 * (∑ y ∈ muSupport A N i, mu A N i y) +
        ∑ y ∈ muSupport A N i, mu A N i y * (g y * g y)) / 2 := by
      calc
        _ = ∑ y ∈ muSupport A N i,
            (mu A N i y * (C ^ 2 + g y * g y)) / 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y ∈ muSupport A N i,
            mu A N i y * (C ^ 2 + g y * g y)) / 2 := by rw [Finset.sum_div]
        _ = ((∑ y ∈ muSupport A N i, mu A N i y * C ^ 2) +
            ∑ y ∈ muSupport A N i, mu A N i y * (g y * g y)) / 2 := by
          congr 1
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
        _ = _ := by
          rw [← Finset.sum_mul]
          ring
    _ = (C ^ 2 * (∑ y ∈ muSupport A N i, mu A N i y * 1) +
        ∑ y ∈ muSupport A N i, mu A N i y * (g y * g y)) / 2 := by
      congr 2
      simp

/-- Uniform bounds pass from generators to their real span for families on `ℕ × ℤ`. -/
theorem bounded_span {S : Set (ℕ → ℤ → ℝ)} {v : ℕ → ℤ → ℝ}
    (hgen : ∀ w ∈ S, ∃ C : ℝ, 0 ≤ C ∧ ∀ N y, |w N y| ≤ C)
    (hv : v ∈ Submodule.span ℝ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N y, |v N y| ≤ C := by
  refine Submodule.span_induction
    (p := fun w _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ N y, |w N y| ≤ C) ?_ ?_ ?_ ?_ hv
  · intro w hw
    exact hgen w hw
  · exact ⟨0, le_rfl, by simp⟩
  · rintro f g _ _ ⟨C, hC, hf⟩ ⟨D, hD, hg⟩
    refine ⟨C + D, add_nonneg hC hD, fun N y => ?_⟩
    calc
      |(f + g) N y| = |f N y + g N y| := rfl
      _ ≤ |f N y| + |g N y| := abs_add_le _ _
      _ ≤ C + D := add_le_add (hf N y) (hg N y)
  · rintro a f _ ⟨C, hC, hf⟩
    refine ⟨|a| * C, mul_nonneg (abs_nonneg _) hC, fun N y => ?_⟩
    change |a * f N y| ≤ |a| * C
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf N y) (abs_nonneg a)

/-- A bounded family of reals has its ultrafilter limit as its actual limit. -/
theorem ulim_tendsto_of_bounded (U : Ultrafilter ℕ) (f : ℕ → ℝ)
    (hbound : ∃ C : ℝ, ∀ N, |f N| ≤ C) :
    Tendsto f (U : Filter ℕ) (𝓝 (ulim U f)) := by
  obtain ⟨C, hC⟩ := hbound
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  let I := Set.Icc (-C) C
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let g : ℕ → I := fun N => ⟨f N, abs_le.mp (hC N)⟩
  let V : Ultrafilter I := Ultrafilter.map g U
  have hV : Tendsto g (U : Filter ℕ) (𝓝 V.lim) := by
    change Filter.map g (U : Filter ℕ) ≤ 𝓝 V.lim
    simpa [V, Ultrafilter.coe_map] using V.le_nhds_lim
  have hf : Tendsto f (U : Filter ℕ) (𝓝 (V.lim : ℝ)) := by
    have hcomp := (continuous_subtype_val.tendsto (V.lim)).comp hV
    have hfg : (fun N => (g N : ℝ)) = f := by
      funext N
      rfl
    rw [← hfg]
    exact hcomp
  have hlim : ulim U f = (V.lim : ℝ) := by
    unfold ulim
    exact hf.limUnder_eq
  simpa [hlim] using hf

open OAI.SourceChartedMenu OAI.SourceFiniteMenu OAI.SourceProductChart

/-- A one-entry charted menu whose nilmanifold is the product of all menu entries. -/
noncomputable def repProductMenu {k s : ℕ} (Fm : Fin k → Menu s) : Menu s where
  size := 1
  G _ := ∀ t, (Fm t).productG
  group _ := inferInstance
  topology _ := inferInstance
  topGroup _ := inferInstance
  Γ _ := OAI.SourceFiniteMenu.productLattice (fun t => (Fm t).productG)
    (fun t => (Fm t).productΓ)
  chart _ := OAI.SourceProductChart.product (fun t => (Fm t).productG)
    (fun t => (Fm t).productΓ) (fun t => (Fm t).productChart)
  metric _ := OAI.SourceFiniteMenu.productMetric (fun t => (Fm t).productG)
    (fun t => (Fm t).productΓ) (fun t => (Fm t).productMetric)
    (fun t => (Fm t).productCompatible)
  compatible _ := OAI.SourceFiniteMenu.productMetric_compatible
    (fun t => (Fm t).productG) (fun t => (Fm t).productΓ)
    (fun t => (Fm t).productMetric) (fun t => (Fm t).productCompatible)

/-- Put a finite family of pieces on the one-entry product menu and combine their observables. -/
noncomputable def repProductPiece {k s : ℕ} {A : Parameters K} {l : Fin K}
    (Fm : Fin k → Menu s) (Km : Fin k → ℝ≥0)
    (Φ : ∀ t, RepFamily A l (Fm t) (Km t))
    (G : (Fin k → ℝ) → ℝ) (L : ℝ≥0) (hG : LipschitzWith L G)
    (hG01 : ∀ x : Fin k → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
      G x ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (q r : ℤ) :
    CosetPiece (repProductMenu Fm) (L * ∑ t, Km t) := by
  let M := repProductMenu Fm
  let Gt : Fin k → Type := fun t => (Fm t).productG
  let Γt : ∀ t, Subgroup (Gt t) := fun t => (Fm t).productΓ
  let met : ∀ t, MetricSpace (Gt t ⧸ Γt t) := fun t => (Fm t).productMetric
  let hmet : ∀ t, QuotientGroup.instTopologicalSpace (Γt t) =
    (met t).toUniformSpace.toTopologicalSpace := fun t => (Fm t).productCompatible
  let metProd := OAI.SourceFiniteMenu.productMetric Gt Γt met hmet
  let hmetProd := OAI.SourceFiniteMenu.productMetric_compatible Gt Γt met hmet
  letI : ∀ t, MetricSpace (Gt t ⧸ Γt t) := fun t => (met t).replaceTopology (hmet t)
  letI : MetricSpace ((∀ t, Gt t) ⧸ OAI.SourceFiniteMenu.productLattice Gt Γt) :=
    metProd.replaceTopology hmetProd
  let qpi := OAI.SourceFiniteMenu.quotientPi Gt Γt
  let P : ∀ t, OAI.SourceMenuLiteral.CosetPiece (Fm t) (Km t) :=
    fun t => (Φ t).piece N q r
  let fvec : C(((∀ t, Gt t) ⧸ OAI.SourceFiniteMenu.productLattice Gt Γt), Fin k → ℝ) :=
    ⟨fun z t => (P t).lift.padObs (qpi z t),
      continuous_pi fun t => (P t).lift.padObs.continuous.comp
        ((continuous_apply t).comp (OAI.SourceFiniteMenu.quotientPi_continuous Gt Γt))⟩
  have hcoord (t : Fin k) : LipschitzWith (Km t) (fun z => fvec z t) := by
    have hproj : LipschitzWith 1 (fun z => qpi z t) :=
      OAI.SourceFiniteMenu.projection_lipschitz Gt Γt met hmet t
    change LipschitzWith (Km t) (fun z => (P t).lift.padObs (qpi z t))
    simpa only [mul_one, Function.comp_def] using ((P t).lift.pad_lip).comp hproj
  have hvec : LipschitzWith (∑ t, Km t) fvec := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)]
    intro t
    have hsumR : (Km t : ℝ) ≤ ∑ u, (Km u : ℝ) :=
      Finset.single_le_sum (fun u hu => NNReal.coe_nonneg _) (Finset.mem_univ t)
    calc
      dist (fvec z t) (fvec w t) ≤ (Km t : ℝ) * dist z w := (hcoord t).dist_le_mul z w
      _ ≤ (∑ u, (Km u : ℝ)) * dist z w :=
        mul_le_mul_of_nonneg_right hsumR dist_nonneg
      _ = (↑(∑ u, Km u)) * dist z w := by simp
  let ob : ((∀ t, Gt t) ⧸ OAI.SourceFiniteMenu.productLattice Gt Γt) →ᵇ ℝ := {
    toContinuousMap := ⟨fun z => G (fvec z), hG.continuous.comp fvec.continuous⟩
    map_bounded' := ⟨1, fun z w => by
      rw [Real.dist_eq]
      have hz := hG01 (fvec z) (fun t => (P t).lift.pad_range (qpi z t))
      have hw := hG01 (fvec w) (fun t => (P t).lift.pad_range (qpi w t))
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2, hw.1, hw.2]⟩ }
  refine {
    index := ⟨0, by simp [repProductMenu]⟩
    g := fun t => (P t).lift.padG
    x := QuotientGroup.mk (fun t => (P t).lift.padX)
    obs := ob
    lip := by
      change LipschitzWith (L * ∑ t, Km t) (fun z => G (fvec z))
      exact hG.comp hvec
    range := fun z => hG01 (fvec z) (fun t => (P t).lift.pad_range (qpi z t)) }

theorem repProductPiece_eval {k s : ℕ} {A : Parameters K} {l : Fin K}
    (Fm : Fin k → Menu s) (Km : Fin k → ℝ≥0)
    (Φ : ∀ t, RepFamily A l (Fm t) (Km t))
    (G : (Fin k → ℝ) → ℝ) (L : ℝ≥0) (hG : LipschitzWith L G)
    (hG01 : ∀ x : Fin k → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
      G x ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (q r m : ℤ) :
    (repProductPiece Fm Km Φ G L hG hG01 N q r).eval m =
      G (fun t => ((Φ t).piece N q r).eval m) := by
  classical
  let Gt : Fin k → Type := fun t => (Fm t).productG
  let Γt : ∀ t, Subgroup (Gt t) := fun t => (Fm t).productΓ
  let P : ∀ t, OAI.SourceMenuLiteral.CosetPiece (Fm t) (Km t) :=
    fun t => (Φ t).piece N q r
  change G (fun t => (P t).lift.padObs
      ((OAI.SourceFiniteMenu.quotientPi Gt Γt
        (QuotientGroup.mk
          (((fun t => (P t).lift.padG) ^ m) * (fun t => (P t).lift.padX)))) t)) =
    G (fun t => (P t).eval m)
  apply congrArg G
  funext t
  rw [OAI.SourceFiniteMenu.quotientPi_mk]
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [(P t).lift.pad_orbit]
  exact OAI.SourceMenuLiteral.CosetPiece.lift_eval (P t) m

end HindmanSumsProducts.Prediction
