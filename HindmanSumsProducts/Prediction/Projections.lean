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
  sorry

/-- Raising the step bound only enlarges the span (`OAI.SourceMenuLiteral.raiseMenu`). -/
theorem repSpan_mono_step (A : Parameters K) (l : Fin K) {s s' : ℕ} (h : s ≤ s') :
    repSpan A l s ≤ repSpan A l s' := by
  sorry

/-- Projection lower bound (05:670–674): a span element `V` with `‖V‖₂ ≤ 1` and
`⟨h, V⟩ ≥ c` forces `‖P_{i,l} h‖₂ ≥ c`, for a bounded family `h`. -/
theorem le_projNorm (A : Parameters K) (U : Ultrafilter ℕ) (i l : Fin K) (s : ℕ)
    (h V : ℕ → ℤ → ℝ) (hb : ∃ C, ∀ N y, |h N y| ≤ C) (hV : V ∈ repSpan A l s)
    (hVn : familyInner A U i V V ≤ 1) :
    familyInner A U i h V ≤ projNorm A U i l s h := by
  sorry

/-- A Lipschitz map of `[0,1]` into itself, applied to a representing family, is a representing
family on the same menu (05:374–376, used for `ψ(S)` at 05:729–731). -/
theorem RepFamily.comp_exists {A : Parameters K} {l : Fin K} {s : ℕ} {Fm : Menu s}
    {Km : ℝ≥0} (Φ : RepFamily A l Fm Km) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hψ01 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ψ x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Ψ : RepFamily A l Fm (L * Km), ∀ N y, Ψ.eval N y = ψ (Φ.eval N y) := by
  sorry

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
  sorry

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
  set_option maxHeartbeats 10000000 in
    set_option maxRecDepth 10000 in
      classical
      have hεsq : 0 < ε ^ 2 := pow_pos hε 2
      let m : ℕ := ⌊(2 : ℝ) / ε ^ 2⌋₊ + 1
      have hm : 0 < m := by dsimp [m]; omega
      have hwidth : 1 / (m : ℝ) < ε ^ 2 / 2 := by
        have hfloor : (2 : ℝ) / ε ^ 2 < (⌊(2 : ℝ) / ε ^ 2⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have hmul := (div_lt_iff₀ hεsq).mp hfloor
        have hmcast : (m : ℝ) = (⌊(2 : ℝ) / ε ^ 2⌋₊ : ℝ) + 1 := by
          simp [m]
        rw [div_lt_iff₀ (by exact_mod_cast hm)]
        rw [hmcast]
        nlinarith
      let codeCount : ℕ := Fintype.card (Fin a × Fin r → Fin (m + 1))
      obtain ⟨K₀, hRamsey⟩ := energy_ramsey n codeCount
      refine ⟨K₀ + 1, ?_⟩
      intro s As hAs A hdiv U F hF
      let e : Fin K₀ ↪ Fin (K₀ + 1) := Fin.castAddEmb 1
      have he_strict {x y : Fin K₀} (hxy : x < y) : e x < e y := by
        exact_mod_cast hxy
      let Label := {q : ℚ // q ∈ As}
      have hcardLabel : Fintype.card Label = As.card := by
        simpa [Label] using (Fintype.card_coe As)
      have hcardLabelLe : Fintype.card Label ≤ a := by rw [hcardLabel]; exact hAs
      let labelIndex : Label ↪ Fin a :=
        (Fintype.equivFin Label).toEmbedding.trans (Fin.castLEEmb hcardLabelLe)
      let codeEquiv : (Fin a × Fin r → Fin (m + 1)) ≃ Fin codeCount :=
        Fintype.equivFin _
      have hrepSpanBound (l : Fin (K₀ + 1)) : repSpan A l s ≤ BoundedFamilies := by
        apply Submodule.span_le.mpr
        intro v hv
        rcases hv with ⟨Fm, Km, Φ, rfl⟩
        refine ⟨1, by norm_num, ?_⟩
        intro N y
        exact repFamily_eval_abs_le_one Φ N y
      have projNormEq (i l : Fin (K₀ + 1)) (g : FamilySpace A U i) :
          projNorm A U i l s g.1 =
            ‖((boundedSubmoduleToHilbertLinear A U i (repSpan A l s)
              (hrepSpanBound l)).range).topologicalClosure.starProjection
                (familyToHilbert A U i g)‖ := by
        let S := repSpan A l s
        let hS := hrepSpanBound l
        let lin := boundedSubmoduleToHilbertLinear A U i S hS
        let Q := lin.range.topologicalClosure
        have hvals :
            (fun u : ℕ → ℤ → ℝ => familyInner A U i g.1 u) ''
                {u | u ∈ S ∧ familyInner A U i u u ≤ 1} =
              (fun u : S => boundedFamilyInner A U i g ⟨u.1, hS u.2⟩) ''
                {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
                  ⟨u.1, hS u.2⟩ ≤ 1} := by
          ext z
          constructor
          · rintro ⟨u, ⟨huS, hu⟩, rfl⟩
            refine ⟨⟨u, huS⟩, ?_, rfl⟩
            simpa [familyInner, boundedFamilyInner] using hu
          · rintro ⟨u, hu, rfl⟩
            refine ⟨u.1, ⟨u.2, ?_⟩, rfl⟩
            simpa [familyInner, boundedFamilyInner] using hu
        unfold projNorm
        calc
          sSup ((fun u : ℕ → ℤ → ℝ => familyInner A U i g.1 u) ''
              {u | u ∈ S ∧ familyInner A U i u u ≤ 1}) =
            sSup ((fun u : S => boundedFamilyInner A U i g ⟨u.1, hS u.2⟩) ''
              {u : S | boundedFamilyInner A U i ⟨u.1, hS u.2⟩
                ⟨u.1, hS u.2⟩ ≤ 1}) := congrArg sSup hvals
          _ = ‖Q.starProjection (familyToHilbert A U i g)‖ := by
            simpa [Q, lin, S] using
              (boundedSubmodule_unit_sup_eq_projection_norm A U i S hS g)
      let mkFamily : ∀ i : Fin (K₀ + 1), Block (K₀ + 1) → Label → Fin r →
          FamilySpace A U i := fun i B q c => by
        refine ⟨(fun N y => F N B q.1 c y), ⟨1, by norm_num, ?_⟩⟩
        intro N y
        have hy := hF N B q.1 c y
        rw [abs_of_nonneg hy.1]
        exact hy.2
      let energyOnBlock : Fin (K₀ + 1) → Fin (K₀ + 1) → Block (K₀ + 1) → Label → Fin r → ℝ :=
        fun i l B q c =>
          let lin := boundedSubmoduleToHilbertLinear A U i (repSpan A l s) (hrepSpanBound l)
          ‖lin.range.topologicalClosure.starProjection
            (familyToHilbert A U i (mkFamily i B q c))‖
      let blockFromParts : (T : Finset (Fin K₀)) → (l i : Fin K₀) → T.Nonempty →
          (∀ t ∈ T, t < l) → l < i → Block (K₀ + 1) := fun T l i hT hTl hli =>
        ⟨e i, ⟨T.image e, ⟨by
          rcases hT with ⟨t, ht⟩
          exact ⟨e t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩,
          by
            intro z hz
            rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
            exact he_strict ((hTl t ht).trans hli)⟩⟩⟩
      let energy : (S : Finset (Fin K₀)) → (hS : 3 ≤ S.card) → Label → Fin r → ℝ :=
        fun S hS q c => by
          let p := finsetSplitMaxTwo S hS
          have hp := finsetSplitMaxTwo_spec S hS
          exact energyOnBlock (e p.2.2) (e p.2.1)
            (blockFromParts p.1 p.2.1 p.2.2 hp.2.1 hp.2.2.1 hp.2.2.2) q c
      have energy_mem_Icc : ∀ S (hS : 3 ≤ S.card) q c,
          energy S hS q c ∈ Set.Icc (0 : ℝ) 1 := by
        intro S hS q c
        dsimp [energy, energyOnBlock, blockFromParts]
        let p := finsetSplitMaxTwo S hS
        let T := p.1
        let l := p.2.1
        let i := p.2.2
        have hp := finsetSplitMaxTwo_spec S hS
        let B : Block (K₀ + 1) :=
          ⟨e i, ⟨T.image e, ⟨by
            rcases hp.2.1 with ⟨t, ht⟩
            exact ⟨e t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩,
            by
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
              exact he_strict ((hp.2.2.1 t ht).trans hp.2.2.2)⟩⟩⟩
        let Srep := repSpan A (e l) s
        let lin := boundedSubmoduleToHilbertLinear A U (e i) Srep (hrepSpanBound (e l))
        let x := familyToHilbert A U (e i) (mkFamily (e i) B q c)
        have hx := familyToHilbert_norm_le_one_of_unitValued A U (e i)
          (mkFamily (e i) B q c) (by intro N y; exact hF N B q.1 c y)
        refine ⟨norm_nonneg _, ?_⟩
        exact (starProjection_norm_le lin.range.topologicalClosure x).trans hx
      let codeAt : Finset (Fin K₀) → (Fin a × Fin r → Fin (m + 1)) :=
        fun S z => if hS : 3 ≤ S.card then
          if hq : ∃ q : Label, labelIndex q = z.1 then
            realEnergyBin m (energy S hS (Classical.choose hq) z.2)
          else 0
        else 0
      let col : Finset (Fin K₀) → Fin codeCount := fun S => codeEquiv (codeAt S)
      obtain ⟨H₀, hHcard, hHhom⟩ := hRamsey col
      let hOrder := H₀.orderEmbOfFin hHcard
      let pad₀ : Fin n → Fin K₀ := fun u => hOrder ⟨2 * u.val, by omega⟩
      let prin₀ : Fin n → Fin K₀ := fun u => hOrder ⟨2 * u.val + 1, by omega⟩
      have hpad₀_mem (u : Fin n) : pad₀ u ∈ H₀ := by
        exact Finset.orderEmbOfFin_mem H₀ hHcard ⟨2 * u.val, by omega⟩
      have hprin₀_mem (u : Fin n) : prin₀ u ∈ H₀ := by
        exact Finset.orderEmbOfFin_mem H₀ hHcard ⟨2 * u.val + 1, by omega⟩
      have hpad₀_prin₀ (u : Fin n) : pad₀ u < prin₀ u := by
        apply hOrder.strictMono
        simp [pad₀, prin₀]
      have hprin₀_pad₀ (u v : Fin n) (huv : u < v) : prin₀ u < pad₀ v := by
        have hpair : (⟨2 * u.val + 1, by omega⟩ : Fin (2 * n)) < ⟨2 * v.val, by omega⟩ := by
          change 2 * u.val + 1 < 2 * v.val
          omega
        exact hOrder.strictMono hpair
      have hprin₀_strict : StrictMono prin₀ := by
        intro u v huv
        have hpair : (⟨2 * u.val + 1, by omega⟩ : Fin (2 * n)) < ⟨2 * v.val + 1, by omega⟩ := by
          change 2 * u.val + 1 < 2 * v.val + 1
          omega
        exact hOrder.strictMono hpair
      have hprin_strict : StrictMono (fun u : Fin n => e (prin₀ u)) := by
        intro u v huv
        exact he_strict (hprin₀_strict huv)
      let pad : Fin n → Fin (K₀ + 1) := fun u => e (pad₀ u)
      let prin : Fin n → Fin (K₀ + 1) := fun u => e (prin₀ u)
      have hpad_prin (u : Fin n) : pad u < prin u := he_strict (hpad₀_prin₀ u)
      have hprin_pad (u v : Fin n) (huv : u < v) : prin u < pad v :=
        he_strict (hprin₀_pad₀ u v huv)
      have binClose (S S' : Finset (Fin K₀)) (hSsub : S ⊆ H₀) (hS'sub : S' ⊆ H₀)
          (hcard : S.card = S'.card) (hSvalid : 3 ≤ S.card) (hS'valid : 3 ≤ S'.card)
          (hupper : S.card ≤ n + 1) (q : Label) (c : Fin r) :
          |energy S hSvalid q c - energy S' hS'valid q c| ≤ ε ^ 2 / 2 := by
        have hcolors := hHhom S S' hSsub hS'sub hcard hSvalid hupper
        have hcodes : codeAt S = codeAt S' := codeEquiv.injective hcolors
        have hcoord := congrFun hcodes (labelIndex q, c)
        have hq : ∃ q' : Label, labelIndex q' = labelIndex q := ⟨q, rfl⟩
        have hchoose : Classical.choose hq = q := by
          exact labelIndex.injective (Classical.choose_spec hq)
        have hbin : realEnergyBin m (energy S hSvalid q c) =
            realEnergyBin m (energy S' hS'valid q c) := by
          simpa [codeAt, hSvalid, hS'valid, hq, hchoose] using hcoord
        exact (realEnergyBin_eq_close hm (energy_mem_Icc S hSvalid q c)
          (energy_mem_Icc S' hS'valid q c) hbin).trans (le_of_lt hwidth)
      let ModelIx := Option (Block (K₀ + 1) × Label × Fin r)
      let modelEquiv : ModelIx ≃ Fin (Fintype.card ModelIx) := Fintype.equivFin _
      let coarseBound (u : Fin n) (v : ModelIx)
          (Fm : Menu s) (Km : ℝ≥0) (Φ : RepFamily A (pad u) Fm Km) : Prop :=
        match v with
        | none => True
        | some t =>
            projNorm A U (prin u) (pad u) s
              (fun N y => F N t.1 t.2.1.1 t.2.2 y - Φ.eval N y) ≤ ε
      have coarseExists (u : Fin n) (j : Fin (Fintype.card ModelIx)) :
          ∃ Fm : Menu s, ∃ Km : ℝ≥0, ∃ Φ : RepFamily A (pad u) Fm Km,
            coarseBound u (modelEquiv.symm j) Fm Km Φ := by
        cases hdecode : modelEquiv.symm j with
        | none =>
            obtain ⟨Fm, Km, Φ, hΦ⟩ := coarse_approximant A U (prin u) (pad u) s
              (fun _ _ => 0) (by intro N y; exact ⟨by norm_num, by norm_num⟩) ε hε
            exact ⟨Fm, Km, Φ, by simp [coarseBound, hdecode]⟩
        | some t =>
            obtain ⟨Fm, Km, Φ, hΦ⟩ := coarse_approximant A U (prin u) (pad u) s
              (fun N y => F N t.1 t.2.1.1 t.2.2 y)
              (by intro N y; exact hF N t.1 t.2.1.1 t.2.2 y) ε hε
            exact ⟨Fm, Km, Φ, by simpa [coarseBound, hdecode] using hΦ⟩
      choose Fm₀ Km₀ Φ₀ hcoarse₀ using coarseExists
      have hcoordLip (j : Fin (Fintype.card ModelIx)) :
          LipschitzWith 1 (fun x : Fin (Fintype.card ModelIx) → ℝ => x j) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simpa using dist_le_pi_dist x y j
      choose Fcommon hcombine using fun u : Fin n =>
        rep_menu_combination A (pad u) (fun j => Fm₀ u j)
      have hcombineCoord (u : Fin n) (j : Fin (Fintype.card ModelIx)) :
          ∃ Km : ℝ≥0, ∃ Ψ : RepFamily A (pad u) (Fcommon u) Km,
            ∀ N y, Ψ.eval N y = (Φ₀ u j).eval N y := by
        have hG01 : ∀ x : Fin (Fintype.card ModelIx) → ℝ,
            (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) → (fun z => z j) x ∈ Set.Icc (0 : ℝ) 1 := by
          intro x hx
          exact hx j
        exact hcombine u (fun t => Km₀ u t) (fun t => Φ₀ u t)
          (fun z => z j) 1 (hcoordLip j) hG01
      choose KmCommon ΦCommon hPhiEval using hcombineCoord
      obtain ⟨dummyMenu, _⟩ := rep_menu_combination A (0 : Fin (K₀ + 1))
        (fun j : Fin 0 => Fin.elim0 j)
      let menus : Fin (n + 1) → Menu s := Fin.cases dummyMenu Fcommon
      let commonMenu := productMenuFamily menus
      have hmenus (u : Fin n) : menus (Fin.succ u) = Fcommon u := rfl
      let lip : ℝ≥0 := ∑ u : Fin n, ∑ j : Fin (Fintype.card ModelIx), KmCommon u j
      have hKm_le (u : Fin n) (j : Fin (Fintype.card ModelIx)) : KmCommon u j ≤ lip := by
        dsimp [lip]
        calc
          KmCommon u j ≤ ∑ j' : Fin (Fintype.card ModelIx), KmCommon u j' :=
            Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)
          _ ≤ ∑ u' : Fin n, ∑ j' : Fin (Fintype.card ModelIx), KmCommon u' j' :=
            Finset.single_le_sum
              (fun _ _ => Finset.sum_nonneg (fun _ _ => zero_le)) (Finset.mem_univ u)
      have raiseEval {l : Fin (K₀ + 1)} {Fm : Menu s} {K K' : ℝ≥0}
          (Φ : RepFamily A l Fm K) (h : K ≤ K') (N : ℕ) (y : ℤ) :
          (Φ.raiseLip h).eval N y = Φ.eval N y := by
        rfl
      let model : (u : Fin n) → Block (K₀ + 1) → ℚ → Fin r →
          RepFamily A (pad u) commonMenu lip := fun u B q c => by
        let slot : ModelIx := if hq : q ∈ As then some (B, ⟨q, hq⟩, c) else none
        let j := modelEquiv slot
        have hmenu := hmenus u
        let Φsrc : RepFamily A (pad u) (menus (Fin.succ u)) (KmCommon u j) :=
          hmenu.symm ▸ ΦCommon u j
        change RepFamily A (pad u) (productMenuFamily menus) lip
        exact (Φsrc.toProductMenu (Fm := menus) (u := Fin.succ u)).raiseLip (hKm_le u j)
      have model_eval (u : Fin n) (B : Block (K₀ + 1)) (q : ℚ) (c : Fin r)
          (hq : q ∈ As) (N : ℕ) (y : ℤ) :
          (model u B q c).eval N y = (Φ₀ u (modelEquiv (some (B, ⟨q, hq⟩, c)))).eval N y := by
        dsimp [model]
        rw [dif_pos hq]
        rw [raiseEval, RepFamily.toProductMenu_eval]
        exact hPhiEval u (modelEquiv (some (B, ⟨q, hq⟩, c))) N y
      refine ⟨pad, prin, hpad_prin, hprin_pad, commonMenu, lip, model, ?_, ?_⟩
      · intro u B hPB q hq c
        have happrox := hcoarse₀ u (modelEquiv (some (B, ⟨q, hq⟩, c)))
        have hbound : projNorm A U (prin u) (pad u) s
            (fun N y => F N B q c y - (model u B q c).eval N y) ≤ ε := by
          have heval : ∀ N y, (model u B q c).eval N y =
              (Φ₀ u (modelEquiv (some (B, ⟨q, hq⟩, c)))).eval N y :=
            fun N y => model_eval u B q c hq N y
          have hcoarseActive : projNorm A U (prin u) (pad u) s
              (fun N y => F N B q c y -
                (Φ₀ u (modelEquiv (some (B, ⟨q, hq⟩, c)))).eval N y) ≤ ε := by
            simpa [coarseBound, modelEquiv] using happrox
          have heq : (fun N y => F N B q c y - (model u B q c).eval N y) =
              (fun N y => F N B q c y -
                (Φ₀ u (modelEquiv (some (B, ⟨q, hq⟩, c)))).eval N y) := by
            funext N y
            rw [heval N y]
          rw [heq]
          exact hcoarseActive
        exact hbound
      · intro u₁ u B hle hPB q hq c
        by_cases huEq : u₁ = u
        · subst u₁
          let j := modelEquiv (some (B, ⟨q, hq⟩, c))
          have happrox : projNorm A U (prin u) (pad u) s
              (fun N y => F N B q c y - (Φ₀ u j).eval N y) ≤ ε := by
            simpa [coarseBound, j, modelEquiv] using hcoarse₀ u j
          have heval : ∀ N y, (model u B q c).eval N y = (Φ₀ u j).eval N y :=
            fun N y => model_eval u B q c hq N y
          have hfun : (fun N y => F N B q c y - (model u B q c).eval N y) =
              (fun N y => F N B q c y - (Φ₀ u j).eval N y) := by
            funext N y
            rw [heval N y]
          rw [hfun]
          exact happrox.trans (by nlinarith [hε])
        · have hu₁u : u₁ < u := lt_of_le_of_ne hle huEq
          let q' : Label := ⟨q, hq⟩
          let j := modelEquiv (some (B, q', c))
          let tailIndex : Finset (Fin n) := Finset.univ.filter (fun v => prin v ∈ B.2.val)
          let tail₀ : Finset (Fin K₀) := tailIndex.image prin₀
          have htailIndex_ne : tailIndex.Nonempty := by
            rcases B.2.property.1 with ⟨t, ht⟩
            obtain ⟨v, hv, htv⟩ := hPB.2 t ht
            have hvB : prin v ∈ B.2.val := by rw [← htv]; exact ht
            exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvB⟩⟩
          have htailIndex_subset : tailIndex ⊆ Finset.Iio u₁ := by
            intro v hv
            have hvB := (Finset.mem_filter.mp hv).2
            obtain ⟨w, hw, hEq⟩ := hPB.2 (prin v) hvB
            have hEq₀ : prin₀ v = prin₀ w := e.injective (by simpa [prin] using hEq)
            have hvw : v = w := hprin₀_strict.injective hEq₀
            simpa [hvw] using hw
          have htailIndex_card : tailIndex.card ≤ u₁.val := by
            calc
              tailIndex.card ≤ (Finset.Iio u₁).card := Finset.card_le_card htailIndex_subset
              _ = u₁.val := by simp
          have htail₀_card : tail₀.card ≤ u₁.val := by
            rw [Finset.card_image_of_injective _ hprin₀_strict.injective]
            exact htailIndex_card
          have htail₀_ne : tail₀.Nonempty := by
            rcases htailIndex_ne with ⟨v, hv⟩
            exact ⟨prin₀ v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
          have htailLt (w : Fin n) (h₁ : u₁ ≤ w) :
              ∀ t ∈ tail₀, t < pad₀ w := by
            intro t ht
            rcases Finset.mem_image.mp ht with ⟨v, hv, rfl⟩
            exact hprin₀_pad₀ v w (lt_of_lt_of_le (Finset.mem_Iio.mp (htailIndex_subset hv)) h₁)
          have hpadLt (w : Fin n) (h₂ : w ≤ u) : pad₀ w < prin₀ u := by
            have hmono : prin₀ w ≤ prin₀ u := by
              by_cases heq : w = u
              · subst w
                exact le_rfl
              · exact le_of_lt (hprin₀_strict (lt_of_le_of_ne h₂ heq))
            exact lt_of_lt_of_le (hpad₀_prin₀ w) hmono
          let enc : Fin n → Finset (Fin K₀) :=
            fun w => insert (pad₀ w) (insert (prin₀ u) tail₀)
          have hpadNotTail (w : Fin n) (h₁ : u₁ ≤ w) : pad₀ w ∉ tail₀ := by
            intro hp
            exact (lt_irrefl (pad₀ w)) (htailLt w h₁ (pad₀ w) hp)
          have hprinNotTail (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              prin₀ u ∉ tail₀ := by
            intro hi
            have hlt := htailLt w h₁ (prin₀ u) hi
            exact (lt_irrefl (prin₀ u)) (hlt.trans (hpadLt w h₂))
          have houterNot (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              pad₀ w ∉ insert (prin₀ u) tail₀ := by
            simp [hpadNotTail w h₁, hprinNotTail w h₁ h₂,
              ne_of_lt (hpadLt w h₂)]
          have hencCard (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              (enc w).card = tail₀.card + 2 := by
            dsimp [enc]
            rw [Finset.card_insert_of_notMem (houterNot w h₁ h₂),
              Finset.card_insert_of_notMem (hprinNotTail w h₁ h₂)]
          have hencValid (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              3 ≤ (enc w).card := by
            rw [hencCard w h₁ h₂]
            have hpos : 1 ≤ tail₀.card := Finset.card_pos.mpr htail₀_ne
            omega
          have hencUpper (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              (enc w).card ≤ n + 1 := by
            rw [hencCard w h₁ h₂]
            have hu₁n := u₁.isLt
            omega
          have hencSub (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) : enc w ⊆ H₀ := by
            intro x hx
            simp only [enc, Finset.mem_insert] at hx
            rcases hx with hx | hx
            · subst x
              exact hpad₀_mem w
            · rcases hx with hx | hx
              · subst x
                exact hprin₀_mem u
              · rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
                exact hprin₀_mem v
          have hencCardEq : (enc u₁).card = (enc u).card := by
            rw [hencCard u₁ le_rfl (le_of_lt hu₁u), hencCard u (le_of_lt hu₁u) le_rfl]
          have henergyBin := binClose (enc u₁) (enc u)
            (hencSub u₁ le_rfl (le_of_lt hu₁u)) (hencSub u (le_of_lt hu₁u) le_rfl)
            hencCardEq (hencValid u₁ le_rfl (le_of_lt hu₁u))
            (hencValid u (le_of_lt hu₁u) le_rfl)
            (hencUpper u₁ le_rfl (le_of_lt hu₁u)) q' c
          have hsplit (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              finsetSplitMaxTwo (enc w) (hencValid w h₁ h₂) =
                (tail₀, pad₀ w, prin₀ u) := by
            simpa [enc] using
              (finsetSplitMaxTwo_eq_insert tail₀ (pad₀ w) (prin₀ u) htail₀_ne
                (htailLt w h₁) (hpadLt w h₂))
          have htailImage : tail₀.image e = B.2.val := by
            calc
              tail₀.image e = tailIndex.image prin := by
                simp [tail₀, prin, Finset.image_image, Function.comp_def]
              _ = B.2.val := by
                apply Finset.Subset.antisymm
                · intro t ht
                  rcases Finset.mem_image.mp ht with ⟨v, hv, rfl⟩
                  exact (Finset.mem_filter.mp hv).2
                · intro t ht
                  obtain ⟨v, hv, htv⟩ := hPB.2 t ht
                  apply Finset.mem_image.mpr
                  refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, htv.symm⟩
                  rw [← htv]
                  exact ht
          let Benc : Block (K₀ + 1) :=
            blockFromParts tail₀ (pad₀ u₁) (prin₀ u) htail₀_ne
              (htailLt u₁ le_rfl) (hpadLt u₁ (le_of_lt hu₁u))
          have hBenc : Benc = B := by
            rcases B with ⟨pivot, tail⟩
            change pivot = prin u ∧ _ at hPB
            rcases hPB with ⟨hpivot, htail⟩
            subst pivot
            apply Sigma.ext
            · rfl
            · exact heq_of_eq (Subtype.ext htailImage)
          have henergyEnc (w : Fin n) (h₁ : u₁ ≤ w) (h₂ : w ≤ u) :
              energy (enc w) (hencValid w h₁ h₂) q' c =
                ‖((boundedSubmoduleToHilbertLinear A U (prin u) (repSpan A (pad w) s)
                    (hrepSpanBound (pad w))).range).topologicalClosure.starProjection
                    (familyToHilbert A U (prin u) (mkFamily (prin u) B q' c))‖ := by
            let p := finsetSplitMaxTwo (enc w) (hencValid w h₁ h₂)
            have hp := finsetSplitMaxTwo_spec (enc w) (hencValid w h₁ h₂)
            let Bsplit := blockFromParts p.1 p.2.1 p.2.2 hp.2.1 hp.2.2.1 hp.2.2.2
            have hparts := hsplit w h₁ h₂
            have hT : p.1 = tail₀ := congrArg Prod.fst hparts
            have hL : p.2.1 = pad₀ w := congrArg Prod.fst (congrArg Prod.snd hparts)
            have hI : p.2.2 = prin₀ u := congrArg Prod.snd (congrArg Prod.snd hparts)
            have hbase : Bsplit.1 = Benc.1 := by
              change e p.2.2 = e (prin₀ u)
              exact congrArg e hI
            have hBsplit : Bsplit = Benc := by
              apply Sigma.ext
              · exact hbase
              · apply (Subtype.heq_iff_coe_eq (fun T => by rw [hbase])).2
                simpa [Bsplit, blockFromParts, Benc] using
                  congrArg (fun T : Finset (Fin K₀) => T.image e) hT
            change energyOnBlock (e p.2.2) (e p.2.1) Bsplit q' c = _
            rw [hI, hL, hBsplit, hBenc]
          have hPadLe : pad u₁ ≤ pad u :=
            le_of_lt (lt_trans (hpad_prin u₁) (hprin_pad u₁ u hu₁u))
          have hdivPad : ∀ N, A.H N (pad u₁) ∣ A.H N (pad u) :=
            fun N => hdiv N (pad u₁) (pad u) hPadLe
          have hspanle : repSpan A (pad u) s ≤ repSpan A (pad u₁) s :=
            repSpan_antitone A s hdivPad
          let linBig := boundedSubmoduleToHilbertLinear A U (prin u) (repSpan A (pad u) s)
            (hrepSpanBound (pad u))
          let linSmall := boundedSubmoduleToHilbertLinear A U (prin u) (repSpan A (pad u₁) s)
            (hrepSpanBound (pad u₁))
          let Qbig := linBig.range.topologicalClosure
          let Qsmall := linSmall.range.topologicalClosure
          have hrangele := boundedSubmodule_range_mono A U (prin u)
            (repSpan A (pad u) s) (repSpan A (pad u₁) s) hspanle
            (hrepSpanBound (pad u)) (hrepSpanBound (pad u₁))
          have hQle : Qbig ≤ Qsmall := by
            exact Submodule.topologicalClosure_mono hrangele
          let g := mkFamily (prin u) B q' c
          let φ := Φ₀ u j
          let sf : FamilySpace A U (prin u) :=
            ⟨φ.eval, ⟨1, by norm_num, by intro N y; exact repFamily_eval_abs_le_one φ N y⟩⟩
          let residual := g - sf
          let x := familyToHilbert A U (prin u) g
          let y := familyToHilbert A U (prin u) sf
          have hmodelSpan : φ.eval ∈ repSpan A (pad u) s := by
            apply Submodule.subset_span
            exact ⟨Fm₀ u j, Km₀ u j, φ, rfl⟩
          have hyBig : y ∈ Qbig := by
            apply linBig.range.le_topologicalClosure
            let v : repSpan A (pad u) s := ⟨φ.eval, hmodelSpan⟩
            change boundedSubmoduleToHilbertLinear A U (prin u) (repSpan A (pad u) s)
                (hrepSpanBound (pad u)) v ∈ linBig.range
            exact ⟨v, rfl⟩
          have hySmall : y ∈ Qsmall := hQle hyBig
          have hresMap : familyToHilbert A U (prin u) residual = x - y := by
            exact (familyToHilbertLinear A U (prin u)).map_sub g sf
          have hfixBig : Qbig.starProjection y = y := Qbig.starProjection_eq_self_iff.mpr hyBig
          have hfixSmall : Qsmall.starProjection y = y :=
            Qsmall.starProjection_eq_self_iff.mpr hySmall
          have hstarBig : Qbig.starProjection (familyToHilbert A U (prin u) residual) =
              Qbig.starProjection x - y := by
            calc
              Qbig.starProjection (familyToHilbert A U (prin u) residual) =
                  Qbig.starProjection (x - y) := by rw [hresMap]
              _ = Qbig.starProjection x - Qbig.starProjection y := map_sub _ _ _
              _ = Qbig.starProjection x - y := by rw [hfixBig]
          have happroxPhi : projNorm A U (prin u) (pad u) s
              (fun N y => F N B q c y - φ.eval N y) ≤ ε := by
            simpa [coarseBound, j, q', modelEquiv] using hcoarse₀ u j
          have hcoarseHilb : ‖Qbig.starProjection x - y‖ ≤ ε := by
            have h := happroxPhi
            rw [show (fun N z => F N B q c z - φ.eval N z) = residual.1 by
              funext N z
              rfl] at h
            rw [projNormEq (prin u) (pad u) residual] at h
            rw [hstarBig] at h
            exact h
          have henergySmall := henergyEnc u₁ le_rfl (le_of_lt hu₁u)
          have henergyBig := henergyEnc u (le_of_lt hu₁u) le_rfl
          have hnormBin :
              |‖Qsmall.starProjection x‖ - ‖Qbig.starProjection x‖| ≤ ε ^ 2 / 2 := by
            rw [← henergySmall, ← henergyBig]
            exact henergyBin
          have hsumNorm : |‖Qsmall.starProjection x‖ + ‖Qbig.starProjection x‖| ≤ 2 := by
            have hsmall := energy_mem_Icc (enc u₁) (hencValid u₁ le_rfl (le_of_lt hu₁u)) q' c
            have hbig := energy_mem_Icc (enc u) (hencValid u (le_of_lt hu₁u) le_rfl) q' c
            rw [henergySmall] at hsmall
            rw [henergyBig] at hbig
            have hnonneg : 0 ≤ ‖Qsmall.starProjection x‖ + ‖Qbig.starProjection x‖ :=
              add_nonneg (norm_nonneg _) (norm_nonneg _)
            have hsmallUpper : ‖Qsmall.starProjection x‖ ≤ 1 := hsmall.2
            have hbigUpper : ‖Qbig.starProjection x‖ ≤ 1 := hbig.2
            rw [abs_of_nonneg hnonneg]
            linarith
          have hpowDiff :
              |‖Qsmall.starProjection x‖ ^ 2 - ‖Qbig.starProjection x‖ ^ 2| ≤ ε ^ 2 := by
            calc
              _ = |‖Qsmall.starProjection x‖ - ‖Qbig.starProjection x‖| *
                  |‖Qsmall.starProjection x‖ + ‖Qbig.starProjection x‖| := by
                    rw [← abs_mul]
                    congr 1
                    ring
              _ ≤ (ε ^ 2 / 2) * 2 :=
                mul_le_mul hnormBin hsumNorm (abs_nonneg _) (by positivity)
              _ = ε ^ 2 := by ring
          have hprojSq := nested_starProjection_energy_difference
            (Qlarge := Qbig) (Qsmall := Qsmall) hQle x
          have hprojSqLe : ‖Qsmall.starProjection x - Qbig.starProjection x‖ ^ 2 ≤ ε ^ 2 := by
            rw [hprojSq]
            exact le_trans (le_abs_self _) hpowDiff
          have hprojDiff : ‖Qsmall.starProjection x - Qbig.starProjection x‖ ≤ ε :=
            (sq_le_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hprojSqLe
          have hstarSmall : Qsmall.starProjection
              (familyToHilbert A U (prin u) residual) = Qsmall.starProjection x - y := by
            calc
              Qsmall.starProjection (familyToHilbert A U (prin u) residual) =
                  Qsmall.starProjection (x - y) := by rw [hresMap]
              _ = Qsmall.starProjection x - Qsmall.starProjection y := map_sub _ _ _
              _ = Qsmall.starProjection x - y := by rw [hfixSmall]
          have hsmallResidual : ‖Qsmall.starProjection x - y‖ ≤ 2 * ε := by
            calc
              ‖Qsmall.starProjection x - y‖ =
                  ‖(Qsmall.starProjection x - Qbig.starProjection x) +
                    (Qbig.starProjection x - y)‖ := by congr 1; abel
              _ ≤ ‖Qsmall.starProjection x - Qbig.starProjection x‖ +
                    ‖Qbig.starProjection x - y‖ := norm_add_le _ _
              _ ≤ ε + ε := add_le_add hprojDiff hcoarseHilb
              _ = 2 * ε := by ring
          have hfineEq : (fun N z => F N B q c z - (model u B q c).eval N z) = residual.1 := by
            funext N z
            dsimp [residual, g, sf, mkFamily]
            rw [model_eval u B q c hq N z]
            rfl
          rw [hfineEq, projNormEq (prin u) (pad u₁) residual, hstarSmall]
          exact hsmallResidual

end

end HindmanSumsProducts.Prediction
