import OAI.Combinatorics.SumProduct.Alignment.RawMenu

/-!
# Missing-corner reconstruction (paper Lemma `lem:cube-corner`), in the form used by §5

Paper: `07_cube_limits.tex` lines 117–208 (statement 117–138, proof 140–168); use site
`05_prediction.tex` lines 288–301 (Lemma `lem:nilsequence-testing`).

On each nilmanifold of a finite menu, the value of a bounded Lipschitz observable at the root
`x_∅ = g^k x` of a linear orbit cube `x_ω = g^(k + ∑_{j∈ω} v j) x` (`ω ⊆ Fin (s+1)`) is
approximated within `ε` by a finite "recipe" `∑_t λ_t ∏_{ω ≠ ∅} φ_{t,ω}(x_ω)` in the other
vertices, with `|φ| ≤ 1` Lipschitz. Finitely many recipes serve all observables with given sup
and Lipschitz bounds, uniformly in `g`, `x`, `k`, `v`.
-/

namespace HindmanSumsProducts

open OAI OAI.SourceRawMenu
open scoped NNReal BoundedContinuousFunction

variable {s : ℕ} (F : Menu s)

/-- The menu metric with its topology made definitionally the quotient topology. -/
abbrev menuMetric (i : Fin F.size) : MetricSpace (F.G i ⧸ F.Γ i) :=
  (F.metric i).replaceTopology (F.compatible i)

/-- One missing-corner recipe on menu entry `i`. -/
structure CornerRecipe (i : Fin F.size) where
  terms : ℕ
  coeff : Fin terms → ℝ
  factor : Fin terms → Finset (Fin (s+1)) → (F.G i ⧸ F.Γ i) →ᵇ ℝ
  bound : ∀ t ω y, |factor t ω y| ≤ 1
  lip : ∃ L : ℝ≥0, ∀ t ω, letI := menuMetric F i; LipschitzWith L (factor t ω)

/-- Evaluation of a recipe on the non-root vertices of a cube `x`. -/
def CornerRecipe.eval {i : Fin F.size} (R : CornerRecipe F i)
    (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) : ℝ :=
  ∑ t, R.coeff t * ∏ ω ∈ (Finset.univ.erase ∅), R.factor t ω (x ω)

namespace CubeCornerInternal

open OAI.CubeFaces

variable {G ι : Type} [Group G] [DecidableEq ι]

def lowerFace (D : Finset ι) (g : G) : Finset ι → G :=
  fun v => if Disjoint D v then g else 1

lemma lowerFace_mem_cube (H : Filtration G) (D I : Finset ι) (k : ℕ) (g : G)
    (hDI : D ⊆ I) (hg : g ∈ H.level (D.card + k)) :
    lowerFace D g ∈ cube H I k := by
  classical
  induction D using Finset.induction_on generalizing I k g with
  | empty =>
      have hg0 : g ∈ H.level k := by simpa using hg
      have hface : face (∅ : Finset ι) g = lowerFace (∅ : Finset ι) g := by
        funext v
        simp [lowerFace, face]
      rw [← hface]
      exact face_mem_cube H (Finset.empty_subset I) (by simpa using hg0)
  | @insert a D ha ih =>
      have haI : a ∈ I := hDI (Finset.mem_insert_self a D)
      have hDI' : D ⊆ I := fun x hx => hDI (Finset.mem_insert_of_mem hx)
      have hg' : g ∈ H.level (D.card + (k + 1)) := by
        simpa [Finset.card_insert_of_notMem ha, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hg
      let f := lowerFace D g
      have hf : f ∈ cube H I (k + 1) := ih I (k + 1) g hDI' hg'
      have hrec : lowerFace (insert a D) g = f * upper a f⁻¹ := by
        funext v
        by_cases hav : a ∈ v
        · simp [lowerFace, f, upper, hav, Finset.disjoint_left]
        · simp [lowerFace, f, upper, hav, Finset.disjoint_left]
      have hupper : upper a f⁻¹ ∈ cube H (insert a I) k := by
        apply map_upper_cube_le H a I k
        exact ⟨f⁻¹, (cube H I (k + 1)).inv_mem hf, rfl⟩
      have hupper' : upper a f⁻¹ ∈ cube H I k := by
        simpa [Finset.insert_eq_of_mem haI] using hupper
      rw [hrec]
      exact (cube H I k).mul_mem
        (cube_shift_le H I (Nat.le_succ k) hf) hupper'

def reflect (I : Finset ι) : (Finset ι → G) →* (Finset ι → G) where
  toFun f v := f (I \ v)
  map_one' := by funext v; rfl
  map_mul' f g := by funext v; rfl

lemma reflect_cube (H : Filtration G) (I : Finset ι) (k : ℕ) :
    cube H I k ≤ (cube H I k).comap (reflect I) := by
  classical
  refine iSup_le fun D => iSup_le fun hDI => ?_
  rintro f ⟨g, hg, rfl⟩
  change reflect I (face D g) ∈ cube H I k
  have hlower : reflect I (face D g) = lowerFace D g := by
    funext v
    have hsub : D ⊆ I \ v ↔ Disjoint D v := by
      rw [Finset.subset_sdiff, Finset.disjoint_left]
      constructor
      · intro h x hx hxv
        exact (h.2 hx) hxv
      · intro h
        exact ⟨hDI, h⟩
    change (if D ⊆ I \ v then g else 1) = _
    simp only [hsub]
    rfl
  rw [hlower]
  exact lowerFace_mem_cube H D I k g hDI hg

lemma corner_unique {s : ℕ} (H : Filtration G) (Γ : Subgroup G)
    (hstep : H.level (s + 1) = ⊥)
    {a b : Finset (Fin (s + 1)) → G}
    (ha : a ∈ cube H Finset.univ 0) (hb : b ∈ cube H Finset.univ 0)
    (heq : ∀ ω, ω.Nonempty → (QuotientGroup.mk (a ω) : G ⧸ Γ) = QuotientGroup.mk (b ω)) :
    (QuotientGroup.mk (a ∅) : G ⧸ Γ) = QuotientGroup.mk (b ∅) := by
  classical
  let I : Finset (Fin (s + 1)) := Finset.univ
  let ar := reflect I a
  let br := reflect I b
  have har : ar ∈ cube H I 0 := reflect_cube H I 0 ha
  have hbr : br ∈ cube H I 0 := reflect_cube H I 0 hb
  let f : Finset (Fin (s + 1)) → G := ar⁻¹ * br
  have hf : f ∈ cube H I 0 := (cube H I 0).mul_mem
    ((cube H I 0).inv_mem har) hbr
  have hlevel : H.level (I.card + 0) ≤ Γ := by
    rw [Finset.card_fin, Nat.add_zero, hstep]
    exact bot_le
  have htop : f I ∈ Γ := CubeRationalCharts.cube_corner_mem
    (H := H) (I := I) (k := 0) (f := f) hf Γ
    (fun ω hω => by
      have hcompl : (I \ ω).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hzero
        have hsub : I ⊆ ω := Finset.sdiff_eq_empty_iff_subset.mp hzero
        exact hω.ne (Finset.Subset.antisymm (Finset.subset_univ _) hsub)
      have hquot := heq (I \ ω) hcompl
      change (ar ω)⁻¹ * br ω ∈ Γ
      simpa [f, ar, br, reflect] using (QuotientGroup.eq.mp hquot)) hlevel
  have hroot : (QuotientGroup.mk (a ∅) : G ⧸ Γ) = QuotientGroup.mk (b ∅) := by
    have hdiff : (a ∅)⁻¹ * b ∅ ∈ Γ := by
      simpa [f, ar, br, I, reflect] using htop
    exact (QuotientGroup.eq (s := Γ) (a := a ∅) (b := b ∅)).mpr hdiff
  exact hroot

lemma compact_cube_quotient {G : Type} {ι : Type} [Group G] [DecidableEq ι]
    [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (H : Filtration G)
    (hrep : ∀ k, CompactGroupProducts.HasCompactReps (H.level k) Γ)
    (I : Finset ι) (k : ℕ) :
    ∃ C : Set (Finset ι → G ⧸ Γ), IsCompact C ∧
      C = Set.range (fun f : cube H I k => fun v => QuotientGroup.mk ((f : Finset ι → G) v)) := by
  classical
  obtain ⟨D, hD, hDC, hrepD⟩ :=
    CubeFaces.cube_hasCompactReps H Γ hrep I k
  let arrQuot (f : Finset ι → G) : Finset ι → G ⧸ Γ := fun v => QuotientGroup.mk (f v)
  have harrCont : Continuous arrQuot :=
    continuous_pi fun v => QuotientGroup.continuous_mk.comp (continuous_apply v)
  let C : Set (Finset ι → G ⧸ Γ) :=
    Set.range (fun f : cube H I k => arrQuot (f : Finset ι → G))
  have hCeq : C = arrQuot '' D := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      obtain ⟨c, hc, hcf⟩ := hrepD f.1 f.2
      refine ⟨c, hc, ?_⟩
      funext v
      exact (QuotientGroup.eq (s := Γ) (a := c v)
        (b := (f : Finset ι → G) v)).mpr (hcf v)
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hDC hc⟩, rfl⟩
  refine ⟨C, ?_, rfl⟩
  rw [hCeq]
  exact hD.image harrCont

lemma chart_level_compact_reps {i : Fin F.size}
    (chart : OAI.SourceProductChart.Chart s (F.G i) (F.Γ i)) :
    ∀ k, CompactGroupProducts.HasCompactReps (chart.filtration.level k) (F.Γ i) := by
  classical
  let q (k : ℕ) : ℕ := (Finset.univ.filter fun j : Fin chart.dim => chart.weight j < k).card
  have hweight (k : ℕ) (j : Fin chart.dim) :
      chart.weight j < k ↔ j.val < q k := by
    by_cases hw : chart.weight j < k
    · have hsub : Finset.Iic j ⊆ Finset.univ.filter
        (fun x : Fin chart.dim => chart.weight x < k) := by
        intro x hx
        simp only [Finset.mem_Iic] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_lt (chart.weight_mono hx) hw
      have hcard : j.val + 1 ≤ q k := by
        simpa [q, Fin.card_Iic] using Finset.card_le_card hsub
      constructor
      · intro _
        omega
      · intro _
        exact hw
    · have hsub : Finset.univ.filter (fun x : Fin chart.dim => chart.weight x < k) ⊆
        Finset.Iio j := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        simp only [Finset.mem_Iio]
        by_contra hjx
        have hle : j ≤ x := le_of_not_gt hjx
        exact hw (lt_of_le_of_lt (chart.weight_mono hle) hx'.2)
      have hcard : q k ≤ j.val := by
        simpa [q, Fin.card_Iio] using Finset.card_le_card hsub
      constructor
      · intro h
        exact (hw h).elim
      · intro h
        omega
  have hlevels (k : ℕ) (g : F.G i) :
      g ∈ chart.filtration.level k ↔
        ∀ j : Fin chart.dim, j.val < q k → chart.coords.coord g j = 0 := by
    rw [chart.level_iff]
    constructor
    · intro hg j hj
      exact hg j ((hweight k j).2 hj)
    · intro hg j hj
      exact hg j ((hweight k j).1 hj)
  have hlattice (g : F.G i) : g ∈ F.Γ i ↔
      ∀ j : Fin chart.dim, ∃ z : ℤ, chart.coords.coord g j = z := by
    exact chart.lattice_iff g
  intro k
  exact OAI.BaseCubeLaw.level_compact_reps chart.coords chart.filtration q hlevels
    (F.Γ i) hlattice k

lemma menu_cube_compact {i : Fin F.size} [IsTopologicalGroup (F.G i)]
    (H : OAI.CubeFaces.Filtration (F.G i))
    (hrep : ∀ k, CompactGroupProducts.HasCompactReps (H.level k) (F.Γ i)) :
    ∃ C : Set (Finset (Fin (s+1)) → F.G i ⧸ F.Γ i), IsCompact C ∧
      C = Set.range (fun f : OAI.CubeFaces.cube H Finset.univ 0 =>
        fun ω => QuotientGroup.mk (f.1 ω)) :=
  compact_cube_quotient (F.Γ i) H hrep (Finset.univ : Finset (Fin (s+1))) 0

lemma linear_lift_mem_cube {s : ℕ} {G : Type} [Group G] [DecidableEq (Fin (s+1))]
    (H : OAI.CubeFaces.Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
    (g x₀ : G) (k : ℤ) (v : Fin (s+1) → ℤ) :
    (fun ω : Finset (Fin (s+1)) => g ^ (k + ∑ j ∈ ω, v j) * x₀) ∈
      OAI.CubeFaces.cube H Finset.univ 0 := by
  classical
  have list_prod_zpow (l : List ℤ) : (l.map fun n => g ^ n).prod = g ^ l.sum := by
    induction l with
    | nil => simp
    | cons n l ih => simp [List.sum_cons, zpow_add, ih]
  let L : List (Finset (Fin (s+1)) → G) := List.ofFn fun j : Fin (s+1) =>
    OAI.CubeFaces.face ({j} : Finset (Fin (s+1))) (g ^ v j)
  let p : Finset (Fin (s+1)) → G := L.prod
  have hp : p ∈ OAI.CubeFaces.cube H Finset.univ 0 := by
    dsimp [p, L]
    apply (OAI.CubeFaces.cube H Finset.univ 0).list_prod_mem
    intro f hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    apply OAI.CubeFaces.face_mem_cube H (by simp)
    simpa [Finset.card_singleton, h1] using (Subgroup.mem_top (g ^ v j))
  have hc : OAI.CubeFaces.face (∅ : Finset (Fin (s+1))) (g ^ k * x₀) ∈
      OAI.CubeFaces.cube H Finset.univ 0 := by
    apply OAI.CubeFaces.face_mem_cube H (Finset.empty_subset _)
    simpa [Finset.card_empty, h0] using (Subgroup.mem_top (g ^ k * x₀))
  have hactive (ω : Finset (Fin (s+1))) :
      (List.ofFn fun j : Fin (s+1) => if j ∈ ω then g ^ (v j) else 1).prod =
        g ^ (∑ j ∈ ω, v j) := by
    let e : List ℤ := List.ofFn fun j : Fin (s+1) => if j ∈ ω then v j else 0
    have hterms : List.ofFn (fun j : Fin (s+1) => if j ∈ ω then g ^ (v j) else 1) =
        e.map fun n => g ^ n := by
      dsimp [e]
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      by_cases hj : j ∈ ω <;> simp [hj]
    have hsum : e.sum = ∑ j ∈ ω, v j := by
      calc
        e.sum = ∑ j : Fin (s+1), if j ∈ ω then v j else 0 := by
          dsimp [e]
          rw [List.sum_ofFn]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin (s+1) => j ∈ ω), v j := by
          rw [← Finset.sum_filter]
        _ = ∑ j ∈ ω, v j := by
          have hfilter : Finset.univ.filter (fun j : Fin (s+1) => j ∈ ω) = ω := by
            ext j
            simp
          rw [hfilter]
    rw [hterms, list_prod_zpow]
    rw [hsum]
  have harray :
      (fun ω : Finset (Fin (s+1)) => g ^ (k + ∑ j ∈ ω, v j) * x₀) =
        p * OAI.CubeFaces.face (∅ : Finset (Fin (s+1))) (g ^ k * x₀) := by
    funext ω
    have hpω : p ω = g ^ (∑ j ∈ ω, v j) := by
      change L.prod ω = _
      rw [Pi.list_prod_apply]
      change (List.map (fun f : Finset (Fin (s+1)) → G => f ω)
        (List.ofFn fun j : Fin (s+1) =>
          OAI.CubeFaces.face ({j} : Finset (Fin (s+1))) (g ^ v j))).prod = _
      rw [List.map_ofFn]
      have hlist : List.ofFn ((fun f : Finset (Fin (s+1)) → G => f ω) ∘
          (fun j : Fin (s+1) =>
            OAI.CubeFaces.face ({j} : Finset (Fin (s+1))) (g ^ v j))) =
          List.ofFn (fun j : Fin (s+1) => if j ∈ ω then g ^ v j else 1) := by
        apply congrArg List.ofFn
        funext j
        simp [OAI.CubeFaces.face_apply, Finset.singleton_subset_iff]
      rw [hlist]
      exact hactive ω
    rw [Pi.mul_apply, hpω]
    simp only [OAI.CubeFaces.face_apply, Finset.empty_subset, ite_true]
    calc
      g ^ (k + ∑ j ∈ ω, v j) * x₀ =
          (g ^ k * g ^ (∑ j ∈ ω, v j)) * x₀ := by rw [zpow_add]
      _ = (g ^ (∑ j ∈ ω, v j) * g ^ k) * x₀ := by
          rw [(Commute.zpow_zpow_self g (∑ j ∈ ω, v j) k).eq]
      _ = g ^ (∑ j ∈ ω, v j) * (g ^ k * x₀) := by rw [mul_assoc]
  rw [harray]
  exact (OAI.CubeFaces.cube H Finset.univ 0).mul_mem hp hc

lemma lipschitz_mul_unit {X : Type} [PseudoMetricSpace X]
    {L₁ L₂ : ℝ≥0} {f g : X → ℝ}
    (hf : LipschitzWith L₁ f) (hg : LipschitzWith L₂ g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    LipschitzWith (L₁ + L₂) (fun x => f x * g x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hfd : |f x - f y| ≤ (L₁ : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hf.dist_le_mul x y
  have hgd : |g x - g y| ≤ (L₂ : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hg.dist_le_mul x y
  rw [Real.dist_eq]
  calc
    |f x * g x - f y * g y|
        = |f x * (g x - g y) + (f x - f y) * g y| := by congr 1 <;> ring
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * ((L₂ : ℝ) * dist x y) + ((L₁ : ℝ) * dist x y) * 1 := by
      apply add_le_add
      · exact mul_le_mul (hfb x) hgd (abs_nonneg _) (by positivity)
      · exact mul_le_mul hfd (hgb y) (abs_nonneg _) (by positivity)
    _ = ((L₁ + L₂ : ℝ≥0) : ℝ) * dist x y := by simp [add_mul, add_comm]

lemma lipschitz_mono {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {L₁ L₂ : ℝ≥0} {f : X → Y} (hf : LipschitzWith L₁ f) (hL : L₁ ≤ L₂) :
    LipschitzWith L₂ f :=
  LipschitzWith.of_dist_le_mul fun x y => (hf.dist_le_mul x y).trans (by gcongr)

noncomputable abbrev recipeConst {i : Fin F.size} (c : ℝ) : CornerRecipe F i := by
  letI := menuMetric F i
  exact {
    terms := 1
    coeff := fun _ => c
    factor := fun _ _ => 1
    bound := by intro t ω y; simp
    lip := by
      refine ⟨0, ?_⟩
      intro t ω
      exact LipschitzWith.of_dist_le_mul fun _ _ => by simp }

noncomputable abbrev recipeAdd {i : Fin F.size} (R S : CornerRecipe F i) : CornerRecipe F i := by
  letI := menuMetric F i
  exact {
    terms := R.terms + S.terms
    coeff := Fin.addCases R.coeff S.coeff
    factor := fun t ω => Fin.addCases (fun j => R.factor j ω) (fun j => S.factor j ω) t
    bound := by
      intro t ω y
      induction t using Fin.addCases with
      | left j => simpa [Fin.addCases] using R.bound j ω y
      | right j => simpa [Fin.addCases] using S.bound j ω y
    lip := by
      obtain ⟨L₁, hL₁⟩ := R.lip
      obtain ⟨L₂, hL₂⟩ := S.lip
      refine ⟨L₁ + L₂, ?_⟩
      intro t ω
      induction t using Fin.addCases with
      | left j =>
          have hL : L₁ ≤ L₁ + L₂ :=
            le_add_of_nonneg_right (show 0 ≤ L₂ by positivity)
          simpa [Fin.addCases] using lipschitz_mono (hL₁ j ω) hL
      | right j =>
          have hL : L₂ ≤ L₁ + L₂ := by
            calc L₂ ≤ L₂ + L₁ := le_add_of_nonneg_right (show 0 ≤ L₁ by positivity)
              _ = L₁ + L₂ := add_comm _ _
          simpa [Fin.addCases] using lipschitz_mono (hL₂ j ω) hL }

noncomputable abbrev recipeMul {i : Fin F.size} (R S : CornerRecipe F i) : CornerRecipe F i := by
  letI := menuMetric F i
  exact {
    terms := R.terms * S.terms
    coeff t :=
      let p := (finProdFinEquiv (m := R.terms) (n := S.terms)).symm t
      R.coeff p.1 * S.coeff p.2
    factor t ω :=
      let p := (finProdFinEquiv (m := R.terms) (n := S.terms)).symm t
      R.factor p.1 ω * S.factor p.2 ω
    bound := by
      intro t ω y
      let p := (finProdFinEquiv (m := R.terms) (n := S.terms)).symm t
      change |R.factor p.1 ω y * S.factor p.2 ω y| ≤ 1
      rw [abs_mul]
      exact mul_le_one₀ (R.bound p.1 ω y) (abs_nonneg _) (S.bound p.2 ω y)
    lip := by
      obtain ⟨L₁, hL₁⟩ := R.lip
      obtain ⟨L₂, hL₂⟩ := S.lip
      refine ⟨L₁ + L₂, ?_⟩
      intro t ω
      let p := (finProdFinEquiv (m := R.terms) (n := S.terms)).symm t
      change LipschitzWith (L₁ + L₂) (fun x => R.factor p.1 ω x * S.factor p.2 ω x)
      exact lipschitz_mul_unit (hL₁ p.1 ω) (hL₂ p.2 ω)
        (R.bound p.1 ω) (S.bound p.2 ω) }

lemma recipeAdd_eval {i : Fin F.size} (R S : CornerRecipe F i)
    (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) :
    (recipeAdd F R S).eval F x = R.eval F x + S.eval F x := by
  classical
  unfold CornerRecipe.eval
  dsimp [recipeAdd]
  rw [Fin.sum_univ_add]
  simp [recipeAdd, Fin.addCases_left, Fin.addCases_right]

lemma recipeMul_eval {i : Fin F.size} (R S : CornerRecipe F i)
    (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) :
    (recipeMul F R S).eval F x = R.eval F x * S.eval F x := by
  classical
  classical
  unfold CornerRecipe.eval
  calc
    _ = ∑ p : Fin R.terms × Fin S.terms,
        (R.coeff p.1 * ∏ ω ∈ Finset.univ.erase ∅, R.factor p.1 ω (x ω)) *
          (S.coeff p.2 * ∏ ω ∈ Finset.univ.erase ∅, S.factor p.2 ω (x ω)) := by
      apply Fintype.sum_equiv (finProdFinEquiv (m := R.terms) (n := S.terms)).symm
      intro t
      simp [recipeMul, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
    _ = (∑ t : Fin R.terms, R.coeff t *
          ∏ ω ∈ Finset.univ.erase ∅, R.factor t ω (x ω)) *
        ∑ t : Fin S.terms, S.coeff t *
          ∏ ω ∈ Finset.univ.erase ∅, S.factor t ω (x ω) := by
      rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

noncomputable def recipeMap {i : Fin F.size} (C : Set
    (Finset (Fin (s+1)) → F.G i ⧸ F.Γ i)) (R : CornerRecipe F i) :
    C({x // x ∈ C}, ℝ) where
  toFun x := R.eval F x.1
  continuous_toFun := by
    apply continuous_finset_sum
    intro t ht
    apply continuous_const.mul
    apply continuous_finset_prod
    intro ω hω
    exact (R.factor t ω).continuous.comp
      ((continuous_apply ω).comp continuous_subtype_val)

noncomputable def distFactor {Q : Type} [MetricSpace Q] (z : Q) : Q →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    { toFun := fun y => dist y z / (1 + dist y z)
      continuous_toFun := by
        have hd : Continuous (fun y : Q => dist y z) := continuous_id.dist continuous_const
        refine hd.div₀ (continuous_const.add hd) ?_
        intro y
        positivity }
    2 (by
      intro x y
      have hx : 0 ≤ dist x z / (1 + dist x z) ∧ dist x z / (1 + dist x z) ≤ 1 := by
        constructor
        · exact div_nonneg dist_nonneg (by positivity)
        · apply (div_le_one (by positivity)).2
          linarith
      have hy : 0 ≤ dist y z / (1 + dist y z) ∧ dist y z / (1 + dist y z) ≤ 1 := by
        constructor
        · exact div_nonneg dist_nonneg (by positivity)
        · apply (div_le_one (by positivity)).2
          linarith
      change |dist x z / (1 + dist x z) - dist y z / (1 + dist y z)| ≤ 2
      exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩)

@[simp] lemma distFactor_apply {Q : Type} [MetricSpace Q] (z y : Q) :
    distFactor z y = dist y z / (1 + dist y z) := rfl

lemma distFactor_bound {Q : Type} [MetricSpace Q] (z y : Q) :
    |distFactor z y| ≤ 1 := by
  rw [distFactor_apply]
  have hdist : 0 ≤ dist y z := dist_nonneg
  have hden : 0 < 1 + dist y z := by positivity
  rw [abs_of_nonneg (div_nonneg hdist (le_of_lt hden))]
  exact (div_le_one hden).2 (by linarith)

lemma distFactor_pos_of_ne {Q : Type} [MetricSpace Q]
    {z y : Q} (h : y ≠ z) : 0 < distFactor z y := by
  rw [distFactor_apply]
  exact div_pos (dist_pos.mpr h) (by positivity)

lemma distFactor_lipschitz {Q : Type} [MetricSpace Q] (z : Q) :
    LipschitzWith 1 (distFactor z) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, distFactor_apply, distFactor_apply]
  let a := dist x z
  let b := dist y z
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hden₁ : 0 < 1 + a := by positivity
  have hden₂ : 0 < 1 + b := by positivity
  have hnum : a / (1 + a) - b / (1 + b) = (a - b) / ((1 + a) * (1 + b)) := by
    field_simp
    ring
  rw [hnum, abs_div, abs_of_pos (mul_pos hden₁ hden₂)]
  calc
    |a - b| / ((1 + a) * (1 + b)) ≤ |a - b| := by
      apply (div_le_iff₀ (mul_pos hden₁ hden₂)).2
      have hden : 1 ≤ (1 + a) * (1 + b) := by nlinarith
      nlinarith [abs_nonneg (a - b)]
    _ = |dist x z - dist y z| := rfl
    _ ≤ (1 : ℝ≥0) * dist x y := by simpa using abs_dist_sub_le x y z

noncomputable abbrev vertexRecipe {i : Fin F.size}
    (ω : Finset (Fin (s+1))) (z : F.G i ⧸ F.Γ i)
    (hω : ω ≠ ∅) : CornerRecipe F i := by
  letI := menuMetric F i
  exact {
    terms := 1
    coeff := fun _ => 1
    factor := fun _ ν => if ν = ω then distFactor z else 1
    bound := by
      intro t ν y
      by_cases hν : ν = ω
      · simpa [hν] using distFactor_bound z y
      · simp [hν]
    lip := by
      refine ⟨1, ?_⟩
      intro t ν
      by_cases hν : ν = ω
      · simpa [hν] using distFactor_lipschitz z
      · apply LipschitzWith.of_dist_le_mul
        intro x y
        simp [hν]
  }

lemma vertexRecipe_eval {i : Fin F.size} (ω : Finset (Fin (s+1)))
    (z : F.G i ⧸ F.Γ i) (hω : ω ≠ ∅)
    (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) :
    (vertexRecipe F ω z hω).eval F x =
      (letI := menuMetric F i; distFactor z (x ω)) := by
  classical
  letI := menuMetric F i
  simp only [CornerRecipe.eval, vertexRecipe, Finset.card_fin]
  have hmem : ω ∈ Finset.univ.erase ∅ := by simp [hω]
  rw [Finset.prod_eq_single ω]
  · simp [Finset.card_fin]
  · intro ν hν hne
    simp [hne]
  · intro hnot
    exact (hnot hmem).elim

lemma recipeConst_eval {i : Fin F.size} (c : ℝ)
  (x : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i) :
    (recipeConst F c).eval F x = c := by
  simp [CornerRecipe.eval, recipeConst, Finset.card_fin]

noncomputable def recipeSubalgebra {i : Fin F.size} (C : Set
    (Finset (Fin (s+1)) → F.G i ⧸ F.Γ i)) :
    Subalgebra ℝ C({x // x ∈ C}, ℝ) where
  carrier := {f | ∃ R : CornerRecipe F i, recipeMap F C R = f}
  zero_mem' := by
    refine ⟨recipeConst F 0, ?_⟩
    ext x
    exact recipeConst_eval F 0 x.1
  one_mem' := by
    refine ⟨recipeConst F 1, ?_⟩
    ext x
    exact recipeConst_eval F 1 x.1
  add_mem' := by
    rintro f g ⟨R, rfl⟩ ⟨S, rfl⟩
    refine ⟨recipeAdd F R S, ?_⟩
    ext x
    exact recipeAdd_eval F R S x.1
  mul_mem' := by
    rintro f g ⟨R, rfl⟩ ⟨S, rfl⟩
    refine ⟨recipeMul F R S, ?_⟩
    ext x
    exact recipeMul_eval F R S x.1
  algebraMap_mem' := by
    intro c
    refine ⟨recipeConst F c, ?_⟩
    ext x
    simp [recipeMap, recipeConst_eval]

lemma recipe_algebra_separates {i : Fin F.size}
    (H : OAI.CubeFaces.Filtration (F.G i)) (hstep : H.level (s+1) = ⊥)
    (C : Set (Finset (Fin (s+1)) → F.G i ⧸ F.Γ i))
    (hC : C = Set.range (fun f : OAI.CubeFaces.cube H Finset.univ 0 =>
      fun ω => QuotientGroup.mk (f.1 ω))) :
    (recipeSubalgebra F C).SeparatesPoints := by
  classical
  letI := menuMetric F i
  letI : CompactSpace (F.G i ⧸ F.Γ i) := F.cocompact i
  intro a b hab
  have hneq : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  have hcoord : ∃ ω, ω ≠ ∅ ∧ a.1 ω ≠ b.1 ω := by
    by_contra hno
    have hsame : ∀ ω, ω ≠ ∅ → a.1 ω = b.1 ω := by
      intro ω hω
      by_contra hdiff
      exact hno ⟨ω, hω, hdiff⟩
    have haRange : a.1 ∈ Set.range (fun f : OAI.CubeFaces.cube H Finset.univ 0 =>
        fun ω => QuotientGroup.mk (f.1 ω)) := hC ▸ a.2
    have hbRange : b.1 ∈ Set.range (fun f : OAI.CubeFaces.cube H Finset.univ 0 =>
        fun ω => QuotientGroup.mk (f.1 ω)) := hC ▸ b.2
    obtain ⟨fa, hfa⟩ := Set.mem_range.mp haRange
    obtain ⟨fb, hfb⟩ := Set.mem_range.mp hbRange
    have hroot : a.1 ∅ = b.1 ∅ := by
      have hcorner := corner_unique H (F.Γ i) hstep fa.2 fb.2 (fun ω hω => by
        calc
          QuotientGroup.mk (fa.1 ω) = a.1 ω := congrFun hfa ω
          _ = b.1 ω := hsame ω (Finset.nonempty_iff_ne_empty.mp hω)
          _ = QuotientGroup.mk (fb.1 ω) := (congrFun hfb ω).symm)
      calc
        a.1 ∅ = QuotientGroup.mk (fa.1 ∅) := (congrFun hfa ∅).symm
        _ = QuotientGroup.mk (fb.1 ∅) := hcorner
        _ = b.1 ∅ := congrFun hfb ∅
    have hall : a.1 = b.1 := by
      funext ω
      by_cases hω : ω = ∅
      · simpa [hω] using hroot
      · exact hsame ω hω
    exact hneq hall
  obtain ⟨ω, hω, hxy⟩ := hcoord
  let R := vertexRecipe F ω (a.1 ω) hω
  let φ := recipeMap F C R
  refine ⟨φ, ⟨φ, ⟨R, rfl⟩, rfl⟩, ?_⟩
  have hzero : distFactor (a.1 ω) (a.1 ω) = 0 := by
    simp [distFactor_apply]
  have hpos := distFactor_pos_of_ne (z := a.1 ω) (y := b.1 ω) hxy.symm
  change R.eval F a.1 ≠ R.eval F b.1
  rw [vertexRecipe_eval F ω (a.1 ω) hω a.1,
    vertexRecipe_eval F ω (a.1 ω) hω b.1]
  exact ne_of_lt (hzero ▸ hpos)

lemma cube_recipe_approx {i : Fin F.size}
    (H : OAI.CubeFaces.Filtration (F.G i)) (hstep : H.level (s+1) = ⊥)
    (C : Set (Finset (Fin (s+1)) → F.G i ⧸ F.Γ i))
    (hC : C = Set.range (fun f : OAI.CubeFaces.cube H Finset.univ 0 =>
      fun ω => QuotientGroup.mk (f.1 ω))) (hcompact : IsCompact C)
    (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : CornerRecipe F i, ∀ x : {p // p ∈ C},
      |R.eval F x.1 - obs (x.1 ∅)| < δ := by
  classical
  letI := menuMetric F i
  letI : CompactSpace (F.G i ⧸ F.Γ i) := F.cocompact i
  letI : CompactSpace {x // x ∈ C} := (isCompact_iff_compactSpace).mp hcompact
  let A := recipeSubalgebra F C
  have hsep : A.SeparatesPoints := recipe_algebra_separates F H hstep C hC
  let rootObs : C({x // x ∈ C}, ℝ) := {
    toFun := fun x => obs (x.1 ∅)
    continuous_toFun := obs.continuous.comp
      ((continuous_apply ∅).comp continuous_subtype_val) }
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      A hsep rootObs δ hδ
  obtain ⟨R, hR⟩ := g.2
  refine ⟨R, ?_⟩
  intro x
  have hnorm := ContinuousMap.norm_coe_le_norm ((g : C({x // x ∈ C}, ℝ)) - rootObs) x
  have hstrict : ‖((g : C({x // x ∈ C}, ℝ)) - rootObs) x‖ < δ :=
    lt_of_le_of_lt hnorm hg
  have hval : ((g : C({x // x ∈ C}, ℝ)) - rootObs) x =
      R.eval F x.1 - obs (x.1 ∅) := by
    change ((g : C({x // x ∈ C}, ℝ)) x - obs (x.1 ∅)) = _
    rw [← hR]
    rfl
  rw [hval, Real.norm_eq_abs] at hstrict
  exact hstrict

lemma cube_corner_entry {i : Fin F.size} (B : ℝ) (K : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (R : Fin m → CornerRecipe F i),
      ∀ (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ), ‖obs‖ ≤ B →
        (letI := menuMetric F i; LipschitzWith K obs) →
        ∃ ρ, ∀ (g : F.G i) (x : F.G i ⧸ F.Γ i) (k : ℤ) (v : Fin (s+1) → ℤ),
          |obs (g ^ k • x) - (R ρ).eval F
            (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ ε := by
  classical
  let M := F.toCharted
  letI : Group (M.G i) := F.group i
  letI : TopologicalSpace (M.G i) := F.topology i
  letI : IsTopologicalGroup (F.G i) := M.topGroup i
  letI : MetricSpace (F.G i ⧸ F.Γ i) := menuMetric F i
  letI : CompactSpace (F.G i ⧸ F.Γ i) := F.cocompact i
  let chart := M.chart i
  let H := chart.filtration
  have hrep : ∀ k, CompactGroupProducts.HasCompactReps (H.level k) (F.Γ i) :=
    chart_level_compact_reps F chart
  obtain ⟨C, hcompact, hC⟩ := menu_cube_compact F H hrep
  let ObsSet : Set (F.G i ⧸ F.Γ i →ᵇ ℝ) :=
    {obs | LipschitzWith K obs ∧ ‖obs‖ ≤ B}
  have hObsCompact : IsCompact (closure ObsSet) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) B)
      (isCompact_closedBall _ _) ObsSet
    · intro f y hf
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (BoundedContinuousFunction.norm_coe_le_norm f y).trans hf.2
    · exact (LipschitzWith.uniformEquicontinuous
        (fun f : ObsSet => (f.1 : F.G i ⧸ F.Γ i → ℝ)) K
        (fun f => f.2.1)).equicontinuous
  let ObsClosure := {f : F.G i ⧸ F.Γ i →ᵇ ℝ // f ∈ closure ObsSet}
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨t, ht⟩ := hObsCompact.elim_finite_subcover
    (fun f : ObsClosure => Metric.ball f.1 δ) (fun _ => Metric.isOpen_ball)
    (by
      intro f hf
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, Metric.mem_ball_self hδ⟩)
  have hrecipes (f : ObsClosure) :
      ∃ R₀ : CornerRecipe F i, ∀ x : {p // p ∈ C},
        |R₀.eval F x.1 - f.1 (x.1 ∅)| < δ :=
    cube_recipe_approx F H chart.step C hC hcompact f.1 δ hδ
  choose R₀ hR₀ using hrecipes
  let m := t.card
  let e := Finset.equivFin t
  let R : Fin m → CornerRecipe F i := fun ρ => R₀ (e.symm ρ)
  refine ⟨m, R, ?_⟩
  intro obs hobs hLip
  have hobsMem : (obs : F.G i ⧸ F.Γ i →ᵇ ℝ) ∈ closure ObsSet :=
    subset_closure ⟨hLip, hobs⟩
  rcases Set.mem_iUnion.mp (ht hobsMem) with ⟨center, hcenter⟩
  rcases Set.mem_iUnion.mp hcenter with ⟨hcenterT, hball⟩
  let ρ : Fin m := e ⟨center, hcenterT⟩
  have hballNorm : ‖obs - center.1‖ < δ := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hball)
  refine ⟨ρ, ?_⟩
  intro g x k v
  let lifted : Finset (Fin (s+1)) → F.G i :=
    fun ω => g ^ (k + ∑ j ∈ ω, v j) * x.out
  have hlifted : lifted ∈ OAI.CubeFaces.cube H Finset.univ 0 := by
    dsimp [lifted]
    apply linear_lift_mem_cube H chart.level0 chart.level1 g x.out k v
  let cubePoint : Finset (Fin (s+1)) → F.G i ⧸ F.Γ i :=
    fun ω => QuotientGroup.mk (lifted ω)
  have hcubePoint : cubePoint ∈ C := by
    rw [hC]
    exact ⟨⟨lifted, hlifted⟩, rfl⟩
  let y : {p // p ∈ C} := ⟨cubePoint, hcubePoint⟩
  have hrootOrbit (n : ℤ) : QuotientGroup.mk (g ^ n * x.out) = g ^ n • x := by
    calc
      QuotientGroup.mk (g ^ n * x.out) = g ^ n • QuotientGroup.mk x.out := rfl
      _ = g ^ n • x := congrArg (fun z => g ^ n • z) (Quotient.out_eq' x)
  have hcubeEq : cubePoint = fun ω => g ^ (k + ∑ j ∈ ω, v j) • x := by
    funext ω
    exact hrootOrbit _
  have hcenterApprox := hR₀ center y
  have hobsPoint : |obs (cubePoint ∅) - center.1 (cubePoint ∅)| < δ := by
    have hle := (obs - center.1).norm_coe_le_norm (cubePoint ∅)
    have hstrict := lt_of_le_of_lt hle hballNorm
    simpa [Real.norm_eq_abs] using hstrict
  have htri :
      |obs (cubePoint ∅) - (R ρ).eval F cubePoint| < δ + δ := by
    have hrecipeEq : R ρ = R₀ center := by
      dsimp [R, ρ]
      simp
    rw [hrecipeEq]
    calc
      |obs (cubePoint ∅) - (R₀ center).eval F cubePoint| =
          |(obs (cubePoint ∅) - center.1 (cubePoint ∅)) +
            (center.1 (cubePoint ∅) - (R₀ center).eval F cubePoint)| := by
              congr 1 <;> ring
      _ ≤ |obs (cubePoint ∅) - center.1 (cubePoint ∅)| +
          |center.1 (cubePoint ∅) - (R₀ center).eval F cubePoint| := abs_add_le _ _
      _ < δ + δ := add_lt_add hobsPoint (by simpa [y, abs_sub_comm] using hcenterApprox)
  have hδsum : δ + δ = ε := by dsimp [δ]; ring
  have hresult : |obs (cubePoint ∅) - (R ρ).eval F cubePoint| < ε := by
    simpa [hδsum] using htri
  have hroot : cubePoint ∅ = g ^ k • x := by
    simpa using congrFun hcubeEq ∅
  rw [← hroot, ← hcubeEq]
  exact le_of_lt hresult

end CubeCornerInternal

/-- Paper Lemma `lem:cube-corner` (07:117–138), in the form used by Lemma
`lem:nilsequence-testing` (05:288–301). -/
theorem cube_corner_recipes (B : ℝ) (K : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : Fin F.size → ℕ) (R : ∀ i, Fin (m i) → CornerRecipe F i),
      ∀ i (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ), ‖obs‖ ≤ B →
        (letI := menuMetric F i; LipschitzWith K obs) →
        ∃ ρ, ∀ (g : F.G i) (x : F.G i ⧸ F.Γ i) (k : ℤ) (v : Fin (s+1) → ℤ),
          |obs (g ^ k • x) - (R i ρ).eval F (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ ε := by
  classical
  have hentry : ∀ i : Fin F.size,
      ∃ m : ℕ, ∃ R : Fin m → CornerRecipe F i,
        ∀ (obs : (F.G i ⧸ F.Γ i) →ᵇ ℝ), ‖obs‖ ≤ B →
          (letI := menuMetric F i; LipschitzWith K obs) →
          ∃ ρ, ∀ (g : F.G i) (x : F.G i ⧸ F.Γ i) (k : ℤ)
              (v : Fin (s+1) → ℤ),
            |obs (g ^ k • x) - (R ρ).eval F
              (fun ω => g ^ (k + ∑ j ∈ ω, v j) • x)| ≤ ε := by
    intro i
    exact CubeCornerInternal.cube_corner_entry F (i := i) B K ε hε
  choose m hm using hentry
  choose R hR using hm
  refine ⟨m, R, ?_⟩
  intro i obs hobs hLip
  exact hR i obs hobs hLip

end HindmanSumsProducts
