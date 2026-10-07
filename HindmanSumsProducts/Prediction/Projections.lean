import HindmanSumsProducts.Prediction.Results
import HindmanSumsProducts.Prediction.PkgE
import HindmanSumsProducts.Prediction.PkgF

/-!
# Nilsequence projections and the Ramsey selection of gap energies (§5.2, 05:355–430)

The paper works in the real Hilbert space of uniformly bounded families with pairing
`lim_𝒰 ⟨·,·⟩_{L²(μ_i)}` (05:355–364) and its closed subspaces `𝒩_{i,l}` spanned by representing
families at gap `l`.  Every statement of §5 uses only norms of projections `‖P_{i,l} v‖₂` of
bounded families `v`, and for a closed span these are
`‖P_{i,l} v‖₂ = sup {⟨v, u⟩ : u ∈ span, ‖u‖₂ ≤ 1}`.
So the statements below use `projNorm`, defined by that supremum, with no completion; the
Hilbert space itself is a device of the proofs (`energy_selection`, `projection_lower_bound`).
In particular (eq:prediction-coarse-approximation) `‖S − P F‖ ≤ ε` with `S ∈ 𝒩` is equivalent to
`‖P(F − S)‖ ≤ ε`, since `P S = S`.
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K r : ℕ}

/-- The pairing `⟨f, g⟩ = lim_𝒰 E_{μ_i} f_N g_N` of 05:356–359. -/
def familyInner (A : Parameters K) (U : Ultrafilter ℕ) (i : Fin K) (f g : ℕ → ℤ → ℝ) : ℝ :=
  ulim U (fun N => Emu A N i (fun y => f N y * g N y))

/-- The span of the representing families at gap `l` of step `≤ s` (all menus, all Lipschitz
bounds); its closure in the Hilbert space is `𝒩_{i,l}` (05:359–364). -/
def repSpan (A : Parameters K) (l : Fin K) (s : ℕ) : Submodule ℝ (ℕ → ℤ → ℝ) :=
  Submodule.span ℝ
    {v | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km), v = Φ.eval}

/-- `‖P_{i,l} v‖₂`, the norm of the orthogonal projection onto `𝒩_{i,l}` (step `≤ s`), for a
bounded family `v`. -/
def projNorm (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (v : ℕ → ℤ → ℝ) : ℝ :=
  sSup ((fun u => familyInner A U i v u) ''
    {u | u ∈ repSpan A l s ∧ familyInner A U i u u ≤ 1})

/-- (eq:prediction-nested-spaces), inclusion part (05:366–373): if `R_l ∣ R_{l'}` then
representing families at gap `l'` are representing families at gap `l` (pieces are re-indexed;
the global progression index is unchanged). -/
theorem repSpan_antitone (A : Parameters K) (s : ℕ) {l l' : Fin K}
    (hdiv : ∀ N, A.H N l ∣ A.H N l') : repSpan A l' s ≤ repSpan A l s := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨Fm, Km, Φ, rfl⟩
  obtain ⟨Ψ, hΨ⟩ := Φ.reindex_of_dvd hdiv
  apply Submodule.subset_span
  refine ⟨Fm, Km, Ψ, ?_⟩
  funext N y
  exact (hΨ N y).symm

/-- Raising the step bound only enlarges the span (`OAI.SourceMenuLiteral.raiseMenu`). -/
theorem repSpan_mono_step (A : Parameters K) (l : Fin K) {s s' : ℕ} (h : s ≤ s') :
    repSpan A l s ≤ repSpan A l s' := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨Fm, Km, Φ, rfl⟩
  apply Submodule.subset_span
  refine ⟨OAI.SourceMenuLiteral.raiseMenu Fm h, Km, Φ.raise h, ?_⟩
  funext N y
  exact (RepFamily.raise_eval Φ h N y).symm

/-- Projection lower bound (05:670–674): a span element `V` with `‖V‖₂ ≤ 1` and
`⟨h, V⟩ ≥ c` forces `‖P_{i,l} h‖₂ ≥ c`, for a bounded family `h`. -/
theorem le_projNorm (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (h V : ℕ → ℤ → ℝ) (hb : ∃ C, ∀ N y, |h N y| ≤ C) (hV : V ∈ repSpan A l s)
    (hVn : familyInner A U i V V ≤ 1) :
    familyInner A U i h V ≤ projNorm A U i l s h := by
  obtain ⟨C, hCb⟩ := hb
  have hC : 0 ≤ C := (abs_nonneg (h 0 0)).trans (hCb 0 0)
  change V ∈ Submodule.span ℝ
    {w | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km), w = Φ.eval} at hV
  have hgen : ∀ w ∈
      {w | ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km), w = Φ.eval},
      ∃ D : ℝ, 0 ≤ D ∧ ∀ N y, |w N y| ≤ D := by
    rintro w ⟨Fm, Km, Φ, rfl⟩
    refine ⟨1, by norm_num, ?_⟩
    intro N y
    simp only [RepFamily.eval]
    let P := Φ.piece N (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))
    change |P.eval ((y - y % (A.M N : ℤ)) / (A.M N : ℤ))| ≤ 1
    have hrange := P.range (P.g ^ ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)
    have hval : |P.obs (P.g ^ ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) • P.x)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hrange.1], hrange.2⟩
    simpa [OAI.SourceMenuLiteral.CosetPiece.eval] using hval
  let S := (fun u => familyInner A U i h u) ''
    {u | u ∈ repSpan A l s ∧ familyInner A U i u u ≤ 1}
  let B : ℝ := (C ^ 2 + 1) / 2
  have hBdd : BddAbove S := by
    refine ⟨B, ?_⟩
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨D, hD, huB⟩ := HindmanSumsProducts.Prediction.bounded_span hgen hu.1
    let m : ℕ → ℝ := fun N => Emu A N i (fun _ => 1)
    let a : ℕ → ℝ := fun N => Emu A N i (fun y => u N y * u N y)
    let b : ℕ → ℝ := fun N => Emu A N i (fun y => h N y * u N y)
    have hm0 : ∀ N, 0 ≤ m N := fun N => by
      exact Emu_nonneg A N i (fun _ => 1) (fun _ => by norm_num)
    have hm1 : ∀ N, m N ≤ 1 := fun N => Emu_mass_le_one A N i
    have ha0 : ∀ N, 0 ≤ a N := fun N => by
      exact Emu_nonneg A N i (fun y => u N y * u N y) (fun _ => mul_self_nonneg _)
    have ha1 : ∀ N, a N ≤ D ^ 2 := by
      intro N
      change Emu A N i (fun y => u N y * u N y) ≤ D ^ 2
      rw [Emu_eq_sum_support]
      calc
        (∑ y ∈ HindmanSumsProducts.Prediction.muSupport A N i,
            mu A N i y * (u N y * u N y)) ≤
          ∑ y ∈ HindmanSumsProducts.Prediction.muSupport A N i,
            mu A N i y * D ^ 2 := by
          apply Finset.sum_le_sum
          intro y hy
          have hy2 : u N y * u N y ≤ D ^ 2 := by
            have habs := abs_le.mp (huB N y)
            nlinarith
          exact mul_le_mul_of_nonneg_left hy2 (mu_nonneg A N i y)
        _ = (∑ y ∈ HindmanSumsProducts.Prediction.muSupport A N i, mu A N i y) * D ^ 2 := by
          rw [← Finset.sum_mul]
        _ = m N * D ^ 2 := by
          have hmEq : m N =
              ∑ y ∈ HindmanSumsProducts.Prediction.muSupport A N i, mu A N i y := by
            dsimp [m]
            rw [Emu_eq_sum_support]
            simp
          rw [hmEq]
        _ ≤ D ^ 2 := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (hm1 N) (sq_nonneg D))
    have hmBound : ∃ E : ℝ, ∀ N, |m N| ≤ E := by
      refine ⟨1, fun N => abs_le.mpr ⟨by linarith [hm0 N], hm1 N⟩⟩
    have haBound : ∃ E : ℝ, ∀ N, |a N| ≤ E := by
      refine ⟨D ^ 2, fun N => abs_le.mpr ⟨by nlinarith [sq_nonneg D, ha0 N], ha1 N⟩⟩
    have hbBound : ∃ E : ℝ, ∀ N, |b N| ≤ E := by
      refine ⟨(C ^ 2 + D ^ 2) / 2, ?_⟩
      intro N
      have hbN := Emu_abs_inner_le A N i (fun y => h N y) (fun y => u N y)
        C hC (fun y => hCb N y)
      have hbN' : |b N| ≤ (C ^ 2 * m N + a N) / 2 := by
        simpa [b, m, a] using hbN
      have hmul : C ^ 2 * m N ≤ C ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left (hm1 N) (sq_nonneg C)]
      have hDsq : 0 ≤ D ^ 2 := sq_nonneg D
      calc
        |b N| ≤ (C ^ 2 * m N + a N) / 2 := hbN'
        _ ≤ (C ^ 2 + D ^ 2) / 2 := by nlinarith [ha1 N, hmul]
    have hmT := HindmanSumsProducts.Prediction.ulim_tendsto_of_bounded U m hmBound
    have haT := HindmanSumsProducts.Prediction.ulim_tendsto_of_bounded U a haBound
    have hbT := HindmanSumsProducts.Prediction.ulim_tendsto_of_bounded U b hbBound
    have hmLim : ulim U m ≤ 1 :=
      le_of_tendsto_of_tendsto' hmT tendsto_const_nhds hm1
    have haLim : ulim U a ≤ 1 := by
      simpa [familyInner, a] using hu.2
    have hqT : Tendsto (fun N => (C ^ 2 * m N + a N) / 2) (U : Filter ℕ)
        (𝓝 ((C ^ 2 * ulim U m + ulim U a) / 2)) := by
      simpa using ((tendsto_const_nhds.mul hmT).add haT).div_const 2
    have hseq : ∀ N, b N ≤ (C ^ 2 * m N + a N) / 2 := by
      intro N
      have hbN := Emu_abs_inner_le A N i (fun y => h N y) (fun y => u N y)
        C hC (fun y => hCb N y)
      have hbN' : |b N| ≤ (C ^ 2 * m N + a N) / 2 := by
        simpa [b, m, a] using hbN
      exact (le_abs_self (b N)).trans hbN'
    have hlim := le_of_tendsto_of_tendsto' hbT hqT hseq
    change ulim U b ≤ B
    dsimp [B]
    calc
      ulim U b ≤ (C ^ 2 * ulim U m + ulim U a) / 2 := hlim
      _ ≤ (C ^ 2 + 1) / 2 := by
        have hc2 : 0 ≤ C ^ 2 := sq_nonneg C
        nlinarith [mul_le_mul_of_nonneg_left hmLim hc2]
  have hmem : familyInner A U i h V ∈ S := by
    exact ⟨V, ⟨hV, hVn⟩, rfl⟩
  exact le_csSup hBdd hmem

/-- A Lipschitz map of `[0,1]` into itself, applied to a representing family, is a representing
family on the same menu (05:374–376, used for `ψ(S)` at 05:729–731). -/
theorem RepFamily.comp_exists {A : Parameters K} {l : Fin K} {s : ℕ} {Fm : Menu s}
    {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Ψ : RepFamily A l Fm (L * Km), ∀ N y, Ψ.eval N y = ψ (Φ.eval N y) := by
  exact Φ.compMap ψ L hψ hψ01

/-- Closure of the model class (02:103–105, 05:374–376, 05:407–419; blueprint X.1): for finitely
many menus of step `≤ s` there is one menu (built from product nilmanifolds of the charted menus)
on which every `[0,1]`-valued Lipschitz combination of representing families on those menus, at
the same gap, is again a representing family.  This includes clipping finite real combinations
to `[0,1]` and re-expressing finitely many families on one common menu. -/
theorem rep_menu_combination (A : Parameters K) (l : Fin K) {k s : ℕ} (Fm : Fin k → Menu s) :
    ∃ F' : Menu s, ∀ (Km : Fin k → ℝ≥0) (Φ : ∀ t, RepFamily A l (Fm t) (Km t))
      (G : (Fin k → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L G →
      (∀ x : Fin k → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → G x ∈ Set.Icc (0 : ℝ) 1) →
      ∃ (K' : ℝ≥0) (Ψ : RepFamily A l F' K'),
        ∀ N y, Ψ.eval N y = G (fun t => (Φ t).eval N y) := by
  refine ⟨repProductMenu Fm, ?_⟩
  intro Km Φ G L hG hG01
  refine ⟨L * ∑ t, Km t, {
    piece := fun N q r => repProductPiece Fm Km Φ G L hG hG01 N q r }, ?_⟩
  intro N y
  change (repProductPiece Fm Km Φ G L hG hG01 N
      (y / (A.H N l : ℤ)) (y % (A.M N : ℤ))).eval
      ((y - y % (A.M N : ℤ)) / (A.M N : ℤ)) =
    G (fun t => (Φ t).eval N y)
  rw [repProductPiece_eval]
  apply congrArg G
  funext t
  simp [RepFamily.eval]

/-- The coarse approximant (05:407–419): a `[0,1]`-valued family `F` has a `[0,1]`-valued
representing family `S` at gap `l` with `‖P_{i,l}(F − S)‖₂ ≤ ε` (approximate `P F` by a finite
combination, clip it to `[0,1]`, Pythagoras). -/
theorem coarse_approximant (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (F : ℕ → ℤ → ℝ) (hF : ∀ N y, F N y ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A l Fm Km),
      projNorm A U i l s (fun N y => F N y - Φ.eval N y) ≤ ε := by
  classical
  let S : Submodule ℝ (ℕ → ℤ → ℝ) := repSpan A l s
  have hS : S ≤ BoundedFamilies := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨Fm, Km, Φ, rfl⟩
    refine ⟨1, by norm_num, ?_⟩
    intro N y
    exact repFamily_eval_abs_le_one Φ N y
  let f : FamilySpace A U i := ⟨F, by
    refine ⟨1, by norm_num, ?_⟩
    intro N y
    rw [abs_of_nonneg (hF N y).1]
    exact (hF N y).2⟩
  let T := boundedSubmoduleToHilbertLinear A U i S hS
  let R := T.range
  let Q := R.topologicalClosure
  let x := familyToHilbert A U i f
  let p := Q.starProjection x
  have hvals :
      (fun u : ℕ → ℤ → ℝ => familyInner A U i F u) ''
          {u | u ∈ S ∧ familyInner A U i u u ≤ 1} =
        (fun u : S => boundedFamilyInner A U i f ⟨u.1, hS u.2⟩) ''
          {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
            ⟨u.1, hS u.2⟩ ≤ 1} := by
    ext a
    constructor
    · rintro ⟨u, ⟨huS, hu⟩, rfl⟩
      refine ⟨⟨u, huS⟩, ?_, ?_⟩
      · simpa [familyInner, boundedFamilyInner, f] using hu
      · rfl
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.1, ⟨u.2, ?_⟩, ?_⟩
      · simpa [familyInner, boundedFamilyInner, f] using hu
      · rfl
  have hprojNorm : projNorm A U i l s F = ‖p‖ := by
    unfold projNorm
    calc
      sSup ((fun u : ℕ → ℤ → ℝ => familyInner A U i F u) ''
          {u | u ∈ S ∧ familyInner A U i u u ≤ 1}) =
        sSup ((fun u : S => boundedFamilyInner A U i f ⟨u.1, hS u.2⟩) ''
          {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
            ⟨u.1, hS u.2⟩ ≤ 1}) := congrArg sSup hvals
      _ = ‖p‖ := by
        simpa [p, Q, R, T, x] using
          (boundedSubmodule_unit_sup_eq_projection_norm A U i S hS f)
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδle : δ ≤ ε := by dsimp [δ]; linarith
  have hpQ : p ∈ Q := Q.starProjection_apply_mem x
  have hpcl : p ∈ closure (R : Set (FamilyHilbertSpace A U i)) := by
    change p ∈ (R.topologicalClosure : Set (FamilyHilbertSpace A U i)) at hpQ
    rw [Submodule.topologicalClosure_coe] at hpQ
    exact hpQ
  obtain ⟨v, hvR, hvclose⟩ := (Metric.mem_closure_iff.mp hpcl) δ hδ
  obtain ⟨u, hTu⟩ := LinearMap.mem_range.mp hvR
  let g : FamilySpace A U i := ⟨u.1, hS u.2⟩
  obtain ⟨k, c, Fm, Km, Ψ₀, hsum⟩ :=
    exists_finite_repFamily_combination (A := A) (l := l) u.2
  let G : (Fin k → ℝ) → ℝ := fun z => clip01 (∑ j, c j * z j)
  obtain ⟨lip, hGLip⟩ := exists_lipschitz_clip_linearCombination c
  have hG01 : ∀ z : Fin k → ℝ, (∀ j, z j ∈ Set.Icc (0 : ℝ) 1) →
      G z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact clip01_mem_Icc _
  obtain ⟨Fm', hcombine⟩ := rep_menu_combination A l Fm
  obtain ⟨Km', Φ, hΦ⟩ := hcombine Km Ψ₀ G lip hGLip hG01
  have hΦclip : ∀ N y, Φ.eval N y = clip01 (u.1 N y) := by
    intro N y
    calc
      Φ.eval N y = G (fun j => (Ψ₀ j).eval N y) := hΦ N y
      _ = clip01 (u.1 N y) := by
        change clip01 (∑ j, c j * (Ψ₀ j).eval N y) = clip01 (u.1 N y)
        rw [← hsum N y]
  have hΦspan : Φ.eval ∈ S := by
    apply Submodule.subset_span
    exact ⟨Fm', Km', Φ, rfl⟩
  let sf : FamilySpace A U i := ⟨Φ.eval, hS hΦspan⟩
  have hresEq : f - sf = familySubClip A U i f g hF := by
    apply Subtype.ext
    funext N y
    change F N y - Φ.eval N y = F N y - clip01 (u.1 N y)
    rw [hΦclip]
  have hcontract : ‖x - familyToHilbert A U i sf‖ ≤
      ‖x - familyToHilbert A U i g‖ := by
    have h := familyToHilbert_clip_contraction A U i f g hF
    have hfg : familyToHilbert A U i (f - g) =
        familyToHilbert A U i f - familyToHilbert A U i g :=
      (familyToHilbertLinear A U i).map_sub f g
    have hfs : familyToHilbert A U i (f - sf) =
        familyToHilbert A U i f - familyToHilbert A U i sf :=
      (familyToHilbertLinear A U i).map_sub f sf
    rw [← hresEq, hfs, hfg] at h
    exact h
  have huR : familyToHilbert A U i g ∈ R := by
    change T u ∈ T.range
    exact ⟨u, rfl⟩
  have hsfR : familyToHilbert A U i sf ∈ R := by
    let us : S := ⟨sf.1, hΦspan⟩
    change T us ∈ T.range
    exact ⟨us, rfl⟩
  have huQ : familyToHilbert A U i g ∈ Q := R.le_topologicalClosure huR
  have hsfQ : familyToHilbert A U i sf ∈ Q := R.le_topologicalClosure hsfR
  have hprojectionDistance := starProjection_sub_of_distance_le Q x
    (familyToHilbert A U i g) (familyToHilbert A U i sf) huQ hsfQ hcontract
  have hsmall : ‖p - familyToHilbert A U i g‖ < δ := by
    have hTg : T u = familyToHilbert A U i g := rfl
    have hgv : familyToHilbert A U i g = v := hTg.symm.trans hTu
    rw [hgv]
    simpa [dist_eq_norm] using hvclose
  have hprojectionResidual :
      ‖Q.starProjection (familyToHilbert A U i (f - sf))‖ ≤ δ := by
    have hstar : Q.starProjection (familyToHilbert A U i (f - sf)) =
        p - familyToHilbert A U i sf := by
      have hmap : familyToHilbert A U i (f - sf) =
          familyToHilbert A U i f - familyToHilbert A U i sf :=
        (familyToHilbertLinear A U i).map_sub f sf
      have hfix : Q.starProjection (familyToHilbert A U i sf) =
          familyToHilbert A U i sf :=
        Q.starProjection_eq_self_iff.mpr hsfQ
      calc
        Q.starProjection (familyToHilbert A U i (f - sf)) =
            Q.starProjection (familyToHilbert A U i f - familyToHilbert A U i sf) :=
          congrArg Q.starProjection hmap
        _ = Q.starProjection (familyToHilbert A U i f) -
            Q.starProjection (familyToHilbert A U i sf) := map_sub _ _ _
        _ = p - familyToHilbert A U i sf := by simp [p, x, hfix]
    rw [hstar]
    exact (hprojectionDistance.trans hsmall.le)
  have hresValues :
      (fun u : ℕ → ℤ → ℝ => familyInner A U i (fun N y => F N y - Φ.eval N y) u) ''
          {u | u ∈ S ∧ familyInner A U i u u ≤ 1} =
        (fun u : S => boundedFamilyInner A U i (f - sf) ⟨u.1, hS u.2⟩) ''
          {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
            ⟨u.1, hS u.2⟩ ≤ 1} := by
    ext a
    constructor
    · rintro ⟨u, ⟨huS, hu⟩, rfl⟩
      refine ⟨⟨u, huS⟩, ?_, ?_⟩
      · simpa [familyInner, boundedFamilyInner] using hu
      · rfl
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.1, ⟨u.2, ?_⟩, ?_⟩
      · simpa [familyInner, boundedFamilyInner] using hu
      · rfl
  have hprojNormResidual :
      projNorm A U i l s (fun N y => F N y - Φ.eval N y) =
        ‖Q.starProjection (familyToHilbert A U i (f - sf))‖ := by
    unfold projNorm
    calc
      sSup ((fun u : ℕ → ℤ → ℝ =>
          familyInner A U i (fun N y => F N y - Φ.eval N y) u) ''
          {u | u ∈ S ∧ familyInner A U i u u ≤ 1}) =
        sSup ((fun u : S => boundedFamilyInner A U i (f - sf)
            ⟨u.1, hS u.2⟩) ''
          {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
            ⟨u.1, hS u.2⟩ ≤ 1}) := congrArg sSup hresValues
      _ = ‖Q.starProjection (familyToHilbert A U i (f - sf))‖ := by
        simpa [Q, R, T] using
          (boundedSubmodule_unit_sup_eq_projection_norm A U i S hS (f - sf))
  refine ⟨Fm', Km', Φ, ?_⟩
  rw [hprojNormResidual]
  exact hprojectionResidual.trans hδle

/-- The Ramsey step of Lemma `lem:energy-selection` (05:399–405): a tuple `(T, l, i)` with
`T < l < i` is identified with the set `T ∪ {l, i}`; for `c` colours there is a master count
`K₀` such that every colouring of subsets has a set `H` of size `2n` on which the colour of a
subset of size `3, …, n+1` depends only on its size. -/
theorem energy_ramsey (n c : ℕ) :
    ∃ K₀ : ℕ, ∀ col : Finset (Fin K₀) → Fin c, ∃ H : Finset (Fin K₀), H.card = 2 * n ∧
      ∀ T T' : Finset (Fin K₀), T ⊆ H → T' ⊆ H → T.card = T'.card → 3 ≤ T.card →
        T.card ≤ n + 1 → col T = col T' := by
  by_cases hc : 0 < c
  · obtain ⟨B, hB, hRamsey⟩ :=
      HindmanSumsProducts.FiniteRamsey.finite_ramsey_simultaneous_subsets
        (n + 2) (2 * n) (fun _ : Fin (n + 2) => c) (fun _ => hc)
    refine ⟨B, ?_⟩
    intro col
    have hlarge : B ≤ (Finset.univ : Finset (Fin B)).card := by
      simpa using (le_of_max_le_right hB)
    obtain ⟨H, hHsub, hHcard, hmono⟩ :=
      hRamsey (Fin B) Finset.univ hlarge (fun _ T => col T)
    refine ⟨H, hHcard, ?_⟩
    intro T T' hTH hT'H hcard hlower hupper
    let m : Fin (n + 2) := ⟨T.card, by omega⟩
    exact hmono m T hTH (by simp [m]) T' hT'H (by simpa [m] using hcard.symm)
  · refine ⟨2 * n, ?_⟩
    intro col
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    exact Fin.elim0 (col ∅)

/-- A master block whose pivot is the principal index `prin u` and whose tail consists of
principal indices `prin v`, `v < u₁` (`u₁ ≤ u`). -/
def PrincipalBlock {n : ℕ} (prin : Fin n → Fin K) (u₁ u : Fin n) (B : Block K) : Prop :=
  B.1 = prin u ∧ ∀ t ∈ B.2.val, ∃ v, v < u₁ ∧ t = prin v

/-- The output of Lemma `lem:energy-selection` (05:378–396) for master parameters `A`, an
ultrafilter `U`, a `[0,1]`-valued family `F`, and `ε`: interleaved indices
`k_1 < j_1 < ⋯ < k_n < j_n` (`pad`, `prin`), one menu of step `≤ s` with one Lipschitz bound, and
`[0,1]`-valued representing families `S_{B,a,c}` at the coarse gap `k_u` for the blocks with pivot
`j_u`, such that (eq:prediction-coarse-approximation) `‖P_{j_u,k_u}(F − S)‖ ≤ ε` and
(eq:prediction-fine-projection) `‖P_{j_u,k_{u₁}}(F − S)‖ ≤ 2ε` whenever the tail consists of
principal indices before `j_{u₁}`, `u₁ ≤ u` (for a chain on the principal indices, `k_{u₁}` is
the padding index immediately before its first pivot). -/
structure EnergySelection (n s : ℕ) (As : Finset ℚ) (A : Parameters K) (U : Ultrafilter ℕ)
    (F : BlockFamily K r) (ε : ℝ) where
  pad : Fin n → Fin K
  prin : Fin n → Fin K
  pad_lt_prin : ∀ u, pad u < prin u
  prin_lt_pad : ∀ u v, u < v → prin u < pad v
  menu : Menu s
  lip : ℝ≥0
  model : (u : Fin n) → Block K → ℚ → Fin r → RepFamily A (pad u) menu lip
  coarse : ∀ (u : Fin n) (B : Block K), PrincipalBlock prin u u B → ∀ a ∈ As, ∀ c : Fin r,
    projNorm A U (prin u) (pad u) s (fun N y => F N B a c y - (model u B a c).eval N y) ≤ ε
  fine : ∀ (u₁ u : Fin n) (B : Block K), u₁ ≤ u → PrincipalBlock prin u₁ u B →
    ∀ a ∈ As, ∀ c : Fin r,
      projNorm A U (prin u) (pad u₁) s (fun N y => F N B a c y - (model u B a c).eval N y) ≤
        2 * ε

/-- Lemma `lem:energy-selection` (05:378–396): for every `ε > 0` a master count `K` depending
only on `n`, `r`, `|𝒜|` and `ε` admits the selection, for every step `s`, every scale list of size
`≤ a`, every master parameters with nested gap lengths, every ultrafilter and every
`[0,1]`-valued family.  The model complexity (menu, Lipschitz bound) depends on all of these. -/
theorem energy_selection (n r a : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (s : ℕ) (As : Finset ℚ), As.card ≤ a → ∀ (A : Parameters K),
      (∀ N (l l' : Fin K), l ≤ l' → A.H N l ∣ A.H N l') →
      ∀ (U : Ultrafilter ℕ) (F : BlockFamily K r), UnitValued F →
        Nonempty (EnergySelection n s As A U F ε) := by
  sorry

end

end HindmanSumsProducts.Prediction
