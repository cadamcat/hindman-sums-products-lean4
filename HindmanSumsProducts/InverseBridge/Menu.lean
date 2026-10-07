import HindmanSumsProducts.InverseBridge.Observable
import HindmanSumsProducts.InverseBridge.Canonical
import HindmanSumsProducts.InverseBridge.SmallModel
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01

/-!
Charted menus and constructors for observable pieces (IB.b1--b3).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceProductChart OAI.SourceMenuLiteral
open Module
open scoped NNReal BoundedContinuousFunction TensorProduct
open scoped Manifold ContDiff Topology

variable {s : ℕ}

private noncomputable def zeroStepModel :
    OAI.Erdos3.RationalFilteredNilmanifold (OAI.Erdos3.RationalTorus.Algebra 0) 0 0 := by
  classical
  let D := OAI.Erdos3.RationalTorus.nilmanifold 0
  letI : Subsingleton (OAI.Erdos3.RationalTorus.Algebra 0) := inferInstance
  have htopbot : (⊤ : Submodule ℚ (OAI.Erdos3.RationalTorus.Algebra 0)) = ⊥ := by
    apply Submodule.eq_bot_of_subsingleton
  have hLayer : D.filtration.layer 1 = ⊥ := by
    rw [D.filtration.one_eq_top]
    exact htopbot
  let F : OAI.Erdos3.NilpotentLieFiltration (OAI.Erdos3.RationalTorus.Algebra 0) 0 := {
    layer := D.filtration.layer
    antitone := D.filtration.antitone
    one_eq_top := D.filtration.one_eq_top
    lie_mem := D.filtration.lie_mem
    terminal := hLayer
  }
  refine ⟨F, D.basis, ?_, ⊤, 1, by omega, ?_, ?_⟩
  · intro i
    exact D.layerBasis ⟨i.val, by omega⟩
  · intro x hx
    simp [OAI.Erdos3.bchSubgroupCoordinates]
  · intro x hx
    change OAI.Erdos3.IntegralVector ((1 : ℚ) • x)
    refine ⟨fun i => 0, ?_⟩
    intro i
    exact Fin.elim0 i

private noncomputable def simpleBaseModel (s : ℕ) :
    OAI.Erdos3.RationalFilteredNilmanifold (OAI.Erdos3.RationalTorus.Algebra 0) s 0 := by
  by_cases hs : s = 0
  · subst s
    exact zeroStepModel
  · exact (OAI.Erdos3.RationalTorus.nilmanifold 0).raiseStep (by omega)

private theorem simpleBaseModel_complexity (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    (simpleBaseModel s).GeometryComplexityLE K₀ := by
  by_cases hs : s = 0
  · subst s
    have hZero : zeroStepModel.GeometryComplexityLE K₀ := by
      dsimp [zeroStepModel, OAI.Erdos3.RationalFilteredNilmanifold.GeometryComplexityLE]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hK₀
      · simpa using Real.one_le_exp hK₀
      · intro i j k
        exact Fin.elim0 i
      · intro i j k
        exact Fin.elim0 k
    simpa [simpleBaseModel] using hZero
  · have hD : (OAI.Erdos3.RationalTorus.nilmanifold 0).GeometryComplexityLE K₀ := by
      exact OAI.Erdos3.RationalTorus.nilmanifold_geometry 0 hK₀ (by norm_num; exact hK₀)
    simpa [simpleBaseModel, hs] using
      (OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_geometry
        (D := OAI.Erdos3.RationalTorus.nilmanifold 0) (by omega) hD)

private noncomputable def pointChart (s : ℕ) :
    OAI.SourceProductChart.Chart s PUnit.{1} (⊤ : Subgroup PUnit.{1}) := by
  classical
  let c : OAI.RationalLattice.RealCoordinates PUnit 0 := {
    coord := Homeomorph.homeomorphOfUnique PUnit (Fin 0 → ℝ)
    one_coord := by intro i; exact Fin.elim0 i
    correction := fun i => Fin.elim0 i
    mul_coord := by intro g h i; exact Fin.elim0 i
  }
  refine {
    dim := 0
    coords := c
    second := ?_
    filtration := {
      level := fun _ => ⊤
      antitone := by intro i j hij; exact le_rfl
      commutator_le := by intro i j; exact le_top
    }
    weight := fun i => Fin.elim0 i
    level_iff := by
      intro k g
      constructor
      · intro _ j hj; exact Fin.elim0 j
      · intro _; exact Subgroup.mem_top g
    weight_pos := by intro i; exact Fin.elim0 i
    lattice_iff := by
      intro g
      constructor
      · intro _ j; exact Fin.elim0 j
      · intro _; exact Subgroup.mem_top g
    weight_mono := by intro i j hij; exact Fin.elim0 i
    level0 := rfl
    level1 := rfl
    step := Subsingleton.elim _ _
  }
  · constructor
    · intro i; exact Fin.elim0 i
    · intro g; exact Subsingleton.elim _ _

private noncomputable def pointMetric :
    MetricSpace (PUnit.{1} ⧸ (⊤ : Subgroup PUnit.{1})) := by
  classical
  let Q := PUnit.{1} ⧸ (⊤ : Subgroup PUnit.{1})
  letI : Subsingleton Q := inferInstance
  letI : PseudoMetricSpace Q :=
    PseudoMetricSpace.induced (fun _ : Q => (PUnit.unit : PUnit.{1}))
      (inferInstance : PseudoMetricSpace PUnit.{1})
  exact MetricSpace.ofT0PseudoMetricSpace Q

private theorem pointMetric_compatible :
    QuotientGroup.instTopologicalSpace (⊤ : Subgroup PUnit.{1}) =
      pointMetric.toUniformSpace.toTopologicalSpace := by
  exact Subsingleton.elim _ _

private theorem point_nilpotent (s : ℕ) :
    (⊤ : Subgroup PUnit.{1}).lowerCentralSeries s = ⊥ := by
  exact Subsingleton.elim _ _

/-- The nilpotent chart theorem used for each linearized model (IB.b1). -/
theorem exists_linearized_chart {d s : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin d))) ∞ G]
    [T2Space G] [SecondCountableTopology G] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Nonempty (Chart s G Γ) := by
  exact OAI.RawLieIntegration.rawChart_of_nilpotent (E₀ := EuclideanSpace ℝ (Fin d)) hstop Γ

/-- A finite collection of canonical linearized models forms one fixed charted menu.
The construction includes the maximum of the observable Lipschitz constants (IB.b2). -/
theorem exists_bridgeMenuData (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ (M : Menu (2 * s)) (K : ℝ≥0)
      (data : Fin M.size → BaseData s),
      0 < M.size ∧ (∀ i, RealizableAt K₀ (data i)) ∧
        ∀ δ, RealizableAt K₀ δ → ∃ i, data i = δ := by
  classical
  let S : Set (BaseData s) := {δ | RealizableAt K₀ δ}
  have hfinite : S.Finite := by
    apply (baseData_finite s K₀).subset
    intro δ hδ
    simpa [S, RealizableAt] using hδ
  let T := {δ : BaseData s // RealizableAt K₀ δ}
  letI : Fintype T := hfinite.fintype
  let n := Fintype.card T
  let e : T ≃ Fin n := Fintype.equivFin T
  let data : Fin n → BaseData s := fun i => (e.symm i).val
  let δ₀ : BaseData s := baseData (simpleBaseModel s)
  have hδ₀ : RealizableAt K₀ δ₀ := by
    refine ⟨OAI.Erdos3.RationalTorus.Algebra 0, inferInstance, inferInstance,
      simpleBaseModel s, simpleBaseModel_complexity s K₀ hK₀, rfl⟩
  have hT : Nonempty T := ⟨⟨δ₀, hδ₀⟩⟩
  have hn : 0 < n := Fintype.card_pos_iff.mpr hT
  let M : Menu (2 * s) := {
    size := n
    G := fun _ => PUnit.{1}
    group := fun _ => inferInstance
    topology := fun _ => inferInstance
    topGroup := fun _ => inferInstance
    Γ := fun _ => ⊤
    chart := fun _ => pointChart (2 * s)
    metric := fun _ => pointMetric
    compatible := fun _ => pointMetric_compatible
  }
  refine ⟨M, 0, ?_, hn, ?_, ?_⟩
  · exact data
  · intro i
    exact (e.symm i).property
  · intro δ hδ
    refine ⟨e ⟨δ, hδ⟩, ?_⟩
    simp [data]

/-- A charted menu selected uniformly from the finite canonical list. -/
noncomputable def bridgeMenu (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) : Menu (2 * s) :=
  Classical.choose (exists_bridgeMenuData s K₀ hK₀)

noncomputable def bridgeMenuLip (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) : ℝ≥0 :=
  Classical.choose (Classical.choose_spec (exists_bridgeMenuData s K₀ hK₀))

noncomputable def bridgeMenuData (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    Fin (bridgeMenu s K₀ hK₀).size → BaseData s :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenuData s K₀ hK₀)))

theorem bridgeMenu_size_pos (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    0 < (bridgeMenu s K₀ hK₀).size :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenuData s K₀ hK₀)))).1

theorem bridgeMenuData_realizable (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (i : Fin (bridgeMenu s K₀ hK₀).size) : RealizableAt K₀ (bridgeMenuData s K₀ hK₀ i) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenuData s K₀ hK₀)))).2.1 i

theorem bridgeMenuData_covers (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (δ : BaseData s)
    (hδ : RealizableAt K₀ δ) : ∃ i, bridgeMenuData s K₀ hK₀ i = δ :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenuData s K₀ hK₀)))).2.2 δ hδ

open OAI OAI.Erdos3 OAI.SourceChartedMenu OAI.SourceMenuLiteral
open OAI.SourceProductChart
open scoped NNReal TensorProduct BoundedContinuousFunction

/-- A constant `[0,1]`-valued piece on any nonempty menu. -/
theorem exists_constPiece {M : Menu s} {K : ℝ≥0} (hM : 0 < M.size)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : CosetPiece M K, ∀ k, P.eval k = c := by
  let i : Fin M.size := ⟨0, by omega⟩
  let obs : (M.G i ⧸ M.Γ i) →ᵇ ℝ := BoundedContinuousFunction.const _ c
  let P : CosetPiece M K := {
    index := i
    g := 1
    x := QuotientGroup.mk 1
    obs := obs
    lip := by
      letI := (M.metric i).replaceTopology (M.compatible i)
      change LipschitzWith K (fun _ : M.G i ⧸ M.Γ i => c)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_self]
      positivity
    range := by
      intro z
      change c ∈ Set.Icc (0 : ℝ) 1
      exact hc
  }
  exact ⟨P, by intro k; simp [P, CosetPiece.eval, obs,
    BoundedContinuousFunction.const_apply']⟩

universe u

/-- The unresolved local construction, tagged by the original finite datum. -/
def DataRepresentation (s : ℕ) (K₀ : ℝ) (δ : BaseData s)
    (M : Menu (2 * s)) (K : ℝ≥0) : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Unit => 1)),
    baseData D = δ → T.normBound ≤ 1 → T.ComplexityLE K₀ →
    ∀ u : ℂ, ‖u‖ = 1 →
      ∃ P : CosetPiece M K, ∀ n : ℤ,
        2 * P.eval n - 1 = (u * T.eval (fun _ => n)).re

/-- The fixed-model geometric obligation; the menu precedes the orbit and H. -/
def FixedModelRepresentation {V : Type} [LieRing V] [LieAlgebra ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    {s d : ℕ} (E : RationalFilteredNilmanifold V s d) (M : Menu (2 * s)) : Prop :=
  ∀ (B : ℝ≥0) (H : E.Space → ℝ), (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) →
    (letI := E.metricSpace; LipschitzWith B H) →
    ∀ p : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ∃ P : CosetPiece M (max 1 B), ∀ n : ℤ,
        P.eval n = H (E.integerOrbitPoint p n)

/-- The integer support side condition of `liftObs_at_integer` is automatic. -/
theorem liftObs_at_integer_auto {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) (n : ℤ) (hr : r x = n) :
    liftObs r point H x = H (point x n) := by
  apply liftObs_at_integer r point H x n hr
  intro m hmn
  by_contra hm
  have hn : bump (r x - n) ≠ 0 := by simp [hr, bump]
  exact hmn (bump_integer_support_subsingleton (r x) hm hn)

/-- Concrete invariance is the only missing algebraic input to this descent.
The inherited scaling, bounds, and range are already proved in Observable. -/
theorem exists_linearized_descent {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (Γ : Subgroup (weightFiltration D.filtration hs).realification.Group)
    (hinv : ∀ H X γ, γ ∈ Γ →
      linearizedObservableLift D hs H (X * γ) = linearizedObservableLift D hs H X) :
    ∃ O : ObservableDescent (weightFiltration D.filtration hs).realification.Group Γ D.Space,
      O.lift = linearizedObservableLift D hs ∧
      ∀ H : D.Space → ℝ, (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) →
        ∀ x, O.desc H x ∈ Set.Icc (0 : ℝ) 1 := by
  let r := fun X : (weightFiltration D.filtration hs).realification.Group =>
    realTranslationCoordinate D.filtration X.coord
  let point := fun X m => linearizedObservablePoint D hs m X
  let O := ObservableDescent.ofLift Γ (linearizedObservableLift D hs) hinv
    (fun c H X => liftObs_scale r point H c X)
    (fun H hH X => liftObs_abs_le_one r point H hH X)
  refine ⟨O, rfl, ?_⟩
  intro H hH x
  refine Quotient.inductionOn x ?_
  intro X
  rw [O.desc_mk]
  exact liftObs_mem_Icc r point H hH X

/-- The observable budget supplies a uniform bound after canonical transport. -/
theorem exists_uniform_rotated_pullback {L V : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing V] [LieAlgebra ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold V s d) (K₀ : ℝ)
    (φ : V ≃ₗ⁅ℚ⁆ L)
    (hbasis : ∀ i, φ (E.basis i) = D.basis i)
    (hlayer : ∀ k a, a ∈ E.filtration.layer k ↔ φ a ∈ D.filtration.layer k)
    (hlattice : E.lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) φ.toLieHom))
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.normBound ≤ 1)
    (hTC : T.ComplexityLE K₀) (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ (p : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (H : E.Space → ℝ),
      (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) ∧
      (letI := E.metricSpace;
        LipschitzWith
          (⟨Real.exp K₀, (Real.exp_pos K₀).le⟩ * coordinateLipschitzBound d d 1 / 2) H) ∧
      ∀ n : ℤ, H (E.integerOrbitPoint p n) =
        (1 + (u * T.eval (fun _ => n)).re) / 2 := by
  obtain ⟨π, hπ, hlift⟩ := exists_transport_map_uniform D E φ hbasis hlayer hlattice
  obtain ⟨p, hp⟩ := hlift T.orbit
  obtain ⟨H, hH, hLH, hOrbit⟩ := transport_to_canonical D E T hT u hu
    π p (coordinateLipschitzBound d d 1) hπ hp
  have hbudget : T.lipBound ≤ (⟨Real.exp K₀, (Real.exp_pos K₀).le⟩ : ℝ≥0) := by
    have hb := RationalFilteredNilmanifold.Niltest.observable_budget hTC
    have hn := T.normBound.coe_nonneg
    change (T.lipBound : ℝ) ≤ Real.exp K₀
    linarith
  refine ⟨p, H, hH, ?_, hOrbit⟩
  letI := E.metricSpace
  exact hLH.weaken (by
    gcongr
    exact mul_le_mul_of_nonneg_right hbudget (by positivity))

/-- A fixed covering model with fixed-model representation gives the local
datum certificate, uniformly across carrier universes and compatible lattices. -/
theorem dataRepresentation_of_cover {V : Type} [LieRing V] [LieAlgebra ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    {s : ℕ} (K₀ : ℝ) (δ : BaseData s)
    (E : RationalFilteredNilmanifold V s δ.d)
    (hcover : ∀ (L : Type u) [LieRing L] [LieAlgebra ℚ L]
      (D : RationalFilteredNilmanifold L s δ.d), baseData D = δ →
      ∃ φ : V ≃ₗ⁅ℚ⁆ L,
        (∀ i, φ (E.basis i) = D.basis i) ∧
        (∀ k a, a ∈ E.filtration.layer k ↔ φ a ∈ D.filtration.layer k) ∧
        E.lattice ≤ D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps
          (hL := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot) φ.toLieHom))
    (M : Menu (2 * s)) (hfixed : FixedModelRepresentation E M) :
    ∃ K : ℝ≥0, DataRepresentation.{u} s K₀ δ M K := by
  let B : ℝ≥0 := ⟨Real.exp K₀, (Real.exp_pos K₀).le⟩ *
    coordinateLipschitzBound δ.d δ.d 1 / 2
  refine ⟨max 1 B, ?_⟩
  intro L _ _ _ _ _ _ d D T hδ hT hTC u hu
  have hd : d = δ.d := congrArg BaseData.d hδ
  subst d
  obtain ⟨φ, hbasis, hlayer, hlattice⟩ := hcover L D hδ
  obtain ⟨p, H, hH, hLH, hOrbit⟩ := exists_uniform_rotated_pullback
    D E K₀ φ hbasis hlayer hlattice T hT hTC u hu
  obtain ⟨P, hP⟩ := hfixed B H hH hLH p
  refine ⟨P, fun n => ?_⟩
  rw [hP n, hOrbit n]
  ring

/-- A finite family of menus admits one menu and one common Lipschitz bound. -/
theorem exists_combinedMenu {s : ℕ} {J : Type} [Fintype J]
    (F : J → Menu s) (B : J → ℝ≥0)
    (hpos : ∃ j, 0 < (F j).size) :
    ∃ (M : Menu s) (K : ℝ≥0), 0 < M.size ∧
      ∀ j (P : CosetPiece (F j) (B j)),
        ∃ Q : CosetPiece M K, ∀ n : ℤ, Q.eval n = P.eval n := by
  classical
  let A := (j : J) × Fin (F j).size
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let M : Menu s := {
    size := Fintype.card A
    G := fun i => (F (e.symm i).1).G (e.symm i).2
    group := fun i => (F (e.symm i).1).group (e.symm i).2
    topology := fun i => (F (e.symm i).1).topology (e.symm i).2
    topGroup := fun i => (F (e.symm i).1).topGroup (e.symm i).2
    Γ := fun i => (F (e.symm i).1).Γ (e.symm i).2
    chart := fun i => (F (e.symm i).1).chart (e.symm i).2
    metric := fun i => (F (e.symm i).1).metric (e.symm i).2
    compatible := fun i => (F (e.symm i).1).compatible (e.symm i).2
  }
  let K : ℝ≥0 := Finset.univ.sup B
  have hB (j : J) : B j ≤ K := Finset.le_sup (Finset.mem_univ j)
  have hM : 0 < M.size := by
    obtain ⟨j, hj⟩ := hpos
    have : Nonempty A := ⟨⟨j, ⟨0, hj⟩⟩⟩
    exact Fintype.card_pos_iff.mpr this
  have transfer (a : A) (i : Fin M.size) (hi : e.symm i = a)
      (g : (F a.1).G a.2) (x : (F a.1).G a.2 ⧸ (F a.1).Γ a.2)
      (obs : ((F a.1).G a.2 ⧸ (F a.1).Γ a.2) →ᵇ ℝ)
      (hlip : letI := ((F a.1).metric a.2).replaceTopology ((F a.1).compatible a.2)
        LipschitzWith (B a.1) obs)
      (hrange : ∀ z, obs z ∈ Set.Icc (0 : ℝ) 1) :
      ∃ Q : CosetPiece M K, ∀ n : ℤ, Q.eval n = obs (g ^ n • x) := by
    subst a
    let Q : CosetPiece M K := {
      index := i
      g := g
      x := x
      obs := obs
      lip := by
        letI := ((F (e.symm i).1).metric (e.symm i).2).replaceTopology
          ((F (e.symm i).1).compatible (e.symm i).2)
        exact hlip.weaken (hB (e.symm i).1)
      range := hrange
    }
    exact ⟨Q, fun _ => rfl⟩
  refine ⟨M, K, hM, ?_⟩
  intro j P
  exact transfer ⟨j, P.index⟩ (e ⟨j, P.index⟩) (e.symm_apply_apply _)
    P.g P.x P.obs P.lip P.range

/-- Once concrete descent and equicontinuity are supplied, the generic metric
theorem constructs an actual charted menu and its observable pieces. -/
theorem exists_menu_of_descent {s : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)]
    [CompactSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)] {Y : Type*} [MetricSpace Y]
    (chart : Chart s G Γ) (O : ObservableDescent G Γ Y)
    (hmetric : QuotientGroup.instTopologicalSpace Γ =
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace)
    (heq : ∀ x ε, 0 < ε →
      ∃ δ, 0 < δ ∧ ∀ y, dist y x < δ → ∀ H : LipOne Y,
        |O.desc H.1 y - O.desc H.1 x| < ε)
    (hrange : ∀ H : Y → ℝ, (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) →
      ∀ x, O.desc H x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ M : Menu s, 0 < M.size ∧
      ∀ (B : ℝ≥0) (H : Y → ℝ), (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) →
        LipschitzWith B H → ∀ (g : G) (x : G ⧸ Γ),
        ∃ P : CosetPiece M (max 1 B),
          ∀ n : ℤ, P.eval n = O.desc H (g ^ n • x) := by
  classical
  obtain ⟨d, hd, hLip⟩ := exists_observable_menuMetric O hmetric heq
  let M : Menu s := {
    size := 1
    G := fun _ => G
    group := fun _ => inferInstance
    topology := fun _ => inferInstance
    topGroup := fun _ => inferInstance
    Γ := fun _ => Γ
    chart := fun _ => chart
    metric := fun _ => d
    compatible := fun _ => hd
  }
  refine ⟨M, by norm_num [M], ?_⟩
  intro B H hH hLH g x
  have hHabs : ∀ y, |H y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (hH y).1]
    exact (hH y).2
  have hcontinuous : @Continuous (G ⧸ Γ) ℝ (QuotientGroup.instTopologicalSpace Γ)
      inferInstance (O.desc H) := by
    letI := d
    have hc := (hLip H hHabs B hLH).continuous
    rw [← hd] at hc
    exact hc
  let obs : @BoundedContinuousFunction (G ⧸ Γ) ℝ
      (QuotientGroup.instTopologicalSpace Γ) inferInstance :=
    BoundedContinuousFunction.mkOfCompact ⟨O.desc H, hcontinuous⟩
  let P : CosetPiece M (max 1 B) := {
    index := ⟨0, by norm_num [M]⟩
    g := g
    x := x
    obs := obs
    lip := by
      letI := d.replaceTopology hd
      have hh := hLip H hHabs B hLH
      rwa [← MetricSpace.replaceTopology_eq d hd] at hh
    range := hrange H hH
  }
  exact ⟨P, fun _ => rfl⟩

/-- The fixed linearized quotient gives one charted menu representing every
normalized Lipschitz observable along every polynomial orbit. -/
theorem exists_linearized_fixedModelRepresentation {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (n : ℕ) (ê : Basis (Fin n) ℚ (Lin D.filtration))
    (grid : ℕ) (GammaHat : Subgroup (weightFiltration D.filtration hs).Group)
    (hgrid : 0 < grid)
    (hcoords : bchSubgroupCoordinates ê GammaHat = scaledIntegerGrid grid)
    (hcoord : ∀ γ ∈ GammaHat,
      ∃ z : ℤ, (rLin D.filtration γ.coord : ℚ) = grid * z)
    (hshift : ∀ z : ℤ,
      (⟨(grid * z : ℚ) • Dhat D.filtration⟩ : (weightFiltration D.filtration hs).Group)
        ∈ GammaHat)
    (hEval : ∀ (g : (weightFiltration D.filtration hs).Group), g ∈ GammaHat →
      rLin D.filtration g.coord = 0 → ∀ m : ℤ,
        (⟨evLin D.filtration m g.coord⟩ : D.filtration.Group) ∈ D.lattice) :
    ∃ M : Menu (2 * s), 0 < M.size ∧ FixedModelRepresentation D M := by
  classical
  let F := D.filtration
  let G := (weightFiltration F hs).realification.Group
  let GammaReal := GammaHat.map (NilpotentLieBCHGroup.realificationHom
    (hnil := (weightFiltration F hs).lowerCentralSeries_eq_bot))
  have houter : bchSubgroupCoordinates ê GammaHat ⊆ denominatorGrid grid := by
    rw [hcoords]
    exact scaledIntegerGrid_le_denominatorGrid grid grid
  have hinner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates ê GammaHat := by
    rw [hcoords]
  obtain ⟨τ, htopAdd, hsmul, hT2, htopGroup, hconnected, hsimply, hclosed, hdiscrete⟩ :=
    exists_realification_topology_of_grid ê GammaHat grid hgrid houter
  letI : TopologicalSpace (ℝ ⊗[ℚ] Lin F) := τ
  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Lin F) := htopAdd
  letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] Lin F) := hsmul
  letI : T2Space (ℝ ⊗[ℚ] Lin F) := hT2
  letI : IsTopologicalGroup G := htopGroup
  letI : ConnectedSpace G := hconnected
  letI : SimplyConnectedSpace G := hsimply
  letI : DiscreteTopology GammaReal := isDiscrete_iff_discreteTopology.mp hdiscrete
  let eR : Basis (Fin n) ℝ (ℝ ⊗[ℚ] Lin F) := ê.baseChange ℝ
  letI : FiniteDimensional ℝ (ℝ ⊗[ℚ] Lin F) := eR.finiteDimensional_of_finite
  letI : ChartedSpace (Fin n → ℝ) G :=
    NilpotentLieBCHGroup.basisChartedSpace
      (hnil := (weightFiltration F hs).realification.lowerCentralSeries_eq_bot) eR
  letI : LieGroup 𝓘(ℝ, Fin n → ℝ) ∞ G :=
    NilpotentLieBCHGroup.lieGroup_basis
      (hnil := (weightFiltration F hs).realification.lowerCentralSeries_eq_bot) eR ∞
  letI : MetricSpace (G ⧸ GammaReal) :=
    realificationQuotientMetricSpace ê GammaHat grid hgrid houter
  letI : CompactSpace (G ⧸ GammaReal) :=
    realificationQuotientMetricSpace_compact ê GammaHat grid hgrid hinner houter
  letI : T2Space (G ⧸ GammaReal) := inferInstance
  letI : MetricSpace D.Space := D.metricSpace
  have hmetric : QuotientGroup.instTopologicalSpace GammaReal =
      (inferInstance : MetricSpace (G ⧸ GammaReal)).toUniformSpace.toTopologicalSpace := by
    exact (realificationQuotientMetricSpace_topology ê GammaHat grid hgrid houter).symm
  have hstop : (⊤ : Subgroup G).lowerCentralSeries (2 * s) = ⊥ :=
    NilpotentLieBCHGroup.lowerCentralSeries_eq_bot
      (hnil := (weightFiltration F hs).realification.lowerCentralSeries_eq_bot)
  have hchart : Nonempty (Chart (2 * s) G GammaReal) :=
    OAI.RawLieIntegration.rawChart_of_nilpotent (E₀ := Fin n → ℝ) hstop GammaReal
  have hinv : ∀ H X γ, γ ∈ GammaReal →
      linearizedObservableLift D hs H (X * γ) = linearizedObservableLift D hs H X := by
    intro H X γ hγ
    exact linearizedObservableLift_invariant D hs grid GammaHat hcoord hshift hEval H X hγ
  obtain ⟨O, hO, hrange⟩ := exists_linearized_descent D hs GammaReal hinv
  have hloc : ∀ X ε, 0 < ε →
      ∃ U ∈ 𝓝 X, ∀ Y ∈ U, ∀ H : LipOne D.Space,
        |O.lift H.1 Y - O.lift H.1 X| < ε := by
    intro X ε hε
    obtain ⟨U, hU, hnear⟩ := linearizedObservableLift_locally_equi D hs X ε hε
    refine ⟨U, hU, ?_⟩
    intro Y hY H
    rw [hO]
    exact hnear Y hY H
  have heq := O.equicontinuous_of_lift hmetric hloc
  obtain ⟨M, hM, hmenu⟩ :=
    exists_menu_of_descent (s := 2 * s) GammaReal (Classical.choice hchart)
      O hmetric heq hrange
  refine ⟨M, hM, ?_⟩
  intro K H hH hK p
  obtain ⟨xhat, hxhat, hxEval⟩ :=
    exists_linearized_basepoint F p.log p.adapted
  let xgroup : G := ⟨xhat⟩
  let x : G ⧸ GammaReal := QuotientGroup.mk xgroup
  let g : G := realTranslationElement F hs 1
  obtain ⟨P, hP⟩ := hmenu K H hH hK g x
  refine ⟨P, ?_⟩
  intro m
  rw [hP m]
  have hxcoord : realTranslationCoordinate F xgroup.coord = 0 := by
    simpa [xgroup, realTranslationCoordinate, hxhat]
  have heval := linearizedObservableLift_orbit_eval D hs H xgroup hxcoord p.log hxEval m
  calc
    O.desc H (g ^ m • x) = O.lift H (g ^ m * xgroup) := by
      rw [show g ^ m • x = QuotientGroup.mk (g ^ m * xgroup) by rfl, O.desc_mk]
    _ = linearizedObservableLift D hs H (g ^ m * xgroup) := by rw [hO]
    _ = H (QuotientGroup.mk
        (⟨VectorPolynomial.eval (fun _ : Unit => (m : ℚ)) p.log⟩ :
          D.filtration.realification.Group)) := by
      simpa [g] using heval
    _ = H (D.integerOrbitPoint p m) := by
      congr 1

/-- Finiteness reduces the frozen theorem to one model menu per original datum.
The local hypothesis is an explicit open obligation, not an axiom. -/
theorem exists_bridgeMenu_of_datawise (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hlocal : ∀ δ : BaseData s,
      (∃ (L : Type u) (hL : LieRing L) (hA : LieAlgebra ℚ L),
        letI : LieRing L := hL
        letI : LieAlgebra ℚ L := hA
        ∃ D : RationalFilteredNilmanifold L s δ.d,
          D.GeometryComplexityLE K₀ ∧ baseData D = δ) →
      ∃ (M : Menu (2 * s)) (K : ℝ≥0),
        0 < M.size ∧ DataRepresentation.{u} s K₀ δ M K) :
    ∃ (M : Menu (2 * s)) (K : ℝ≥0), 0 < M.size ∧
      ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
        (D : RationalFilteredNilmanifold L s d)
        (T : D.Niltest (fun _ : Unit => 1)),
        T.normBound ≤ 1 → T.ComplexityLE K₀ →
        ∀ u : ℂ, ‖u‖ = 1 →
          ∃ P : CosetPiece M K, ∀ n : ℤ,
            2 * P.eval n - 1 = (u * T.eval (fun _ => n)).re := by
  classical
  let S : Set (BaseData s) := {δ |
    ∃ (L : Type u) (hL : LieRing L) (hA : LieAlgebra ℚ L),
      letI : LieRing L := hL
      letI : LieAlgebra ℚ L := hA
      ∃ D : RationalFilteredNilmanifold L s δ.d,
        D.GeometryComplexityLE K₀ ∧ baseData D = δ}
  have hfinite : S.Finite := baseData_finite s K₀
  let J := {δ : BaseData s // δ ∈ S}
  letI : Fintype J := hfinite.fintype
  have hchoice : ∀ a : J, ∃ (M : Menu (2 * s)) (K : ℝ≥0),
      0 < M.size ∧ DataRepresentation.{u} s K₀ a.val M K :=
    fun a => hlocal a.val a.property
  choose F B hF using hchoice
  obtain ⟨M₀, B₀, data, hM₀, _⟩ := exists_bridgeMenuData s K₀ hK₀
  let F' : Option J → Menu (2 * s) := fun a => a.elim M₀ F
  let B' : Option J → ℝ≥0 := fun a => a.elim B₀ B
  obtain ⟨M, K, hM, hcombine⟩ := exists_combinedMenu F' B' ⟨none, hM₀⟩
  refine ⟨M, K, hM, ?_⟩
  intro L hL hA _ _ _ _ d D T hT hTC u hu
  have hδ : baseData D ∈ S := ⟨L, hL, hA, D, hTC.1, rfl⟩
  let a : J := ⟨baseData D, hδ⟩
  obtain ⟨P, hP⟩ := (hF a).2 D T rfl hT hTC u hu
  obtain ⟨Q, hQ⟩ := hcombine (some a) P
  exact ⟨Q, fun n => by rw [hQ n]; exact hP n⟩

/-- The step-zero instance of the frozen statement is unconditional. -/
theorem exists_bridgeMenu_zero (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ (M : Menu (2 * 0)) (K : ℝ≥0), 0 < M.size ∧
      ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
        (D : RationalFilteredNilmanifold L 0 d)
        (T : D.Niltest (fun _ : Unit => 1)),
        T.normBound ≤ 1 → T.ComplexityLE K₀ →
        ∀ u : ℂ, ‖u‖ = 1 →
          ∃ P : CosetPiece M K, ∀ n : ℤ,
            2 * P.eval n - 1 = (u * T.eval (fun _ => n)).re := by
  obtain ⟨M, K, data, hM, _⟩ := exists_bridgeMenuData 0 K₀ hK₀
  refine ⟨M, K, hM, ?_⟩
  intro L _ _ _ _ _ _ d D T hT _ u hu
  let c : ℂ := T.observable (QuotientGroup.mk (1 : D.RealGroup))
  have hnorm : ‖u * c‖ ≤ 1 := by
    calc
      ‖u * c‖ = ‖c‖ := by rw [norm_mul, hu, one_mul]
      _ ≤ (T.normBound : ℝ) := T.norm_le _
      _ ≤ 1 := by exact_mod_cast hT
  have hre : |(u * c).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hnorm
  have hrange : (1 + (u * c).re) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
  obtain ⟨P, hP⟩ := exists_constPiece (K := K) hM _ hrange
  refine ⟨P, ?_⟩
  intro n
  rw [hP n, RationalFilteredNilmanifold.Niltest.eval_step_zero]
  dsimp [c]
  ring

/-- No niltest fits a zero complexity budget, so this instance is vacuous. -/
theorem exists_bridgeMenu_budget_zero (s : ℕ) :
    ∃ (M : Menu (2 * s)) (K : ℝ≥0), 0 < M.size ∧
      ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
        (D : RationalFilteredNilmanifold L s d)
        (T : D.Niltest (fun _ : Unit => 1)),
        T.normBound ≤ 1 → T.ComplexityLE 0 →
        ∀ u : ℂ, ‖u‖ = 1 →
          ∃ P : CosetPiece M K, ∀ n : ℤ,
            2 * P.eval n - 1 = (u * T.eval (fun _ => n)).re := by
  obtain ⟨M, K, data, hM, _⟩ := exists_bridgeMenuData s 0 le_rfl
  refine ⟨M, K, hM, ?_⟩
  intro L _ _ _ _ _ _ d D T _ hT u _
  have h := RationalFilteredNilmanifold.Niltest.observable_budget hT
  simp only [Real.exp_zero] at h
  have hn := T.normBound.coe_nonneg
  have hl := T.lipBound.coe_nonneg
  exfalso
  linarith


/-- The finite canonical charted menu represents every bounded observable on every
degree-s nilmanifold, uniformly over unit phases (IB.b2). -/
theorem exists_bridgeMenu (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ (M : Menu (2 * s)) (K : ℝ≥0), 0 < M.size ∧
      ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
        (D : RationalFilteredNilmanifold L s d)
        (T : D.Niltest (fun _ : Unit => 1)),
        T.normBound ≤ 1 → T.ComplexityLE K₀ →
        ∀ u : ℂ, ‖u‖ = 1 →
          ∃ P : CosetPiece M K, ∀ n : ℤ,
            2 * P.eval n - 1 = (u * T.eval (fun _ => n)).re := by
  by_cases hs : s = 0
  · subst s
    exact exists_bridgeMenu_zero K₀ hK₀
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    refine exists_bridgeMenu_of_datawise s K₀ hK₀ ?_
    intro δ hrealizable
    obtain ⟨L, hL, hA, D, _, hDdata⟩ := hrealizable
    letI : LieRing L := hL
    letI : LieAlgebra ℚ L := hA
    obtain ⟨V, hV, hVA, W, hWD, _⟩ := exists_small_model D
    letI : LieRing V := hV
    letI : LieAlgebra ℚ V := hVA
    have hWdata : baseData W = δ := hWD.trans hDdata
    obtain ⟨E, _, _, _, hEcoords, hcover⟩ :=
      exists_canonical_covering_model W
    obtain ⟨τ, htopAdd, hsmul, hT2, _, _, _, _, _⟩ :=
      exists_realification_topology_of_grid E.basis E.lattice E.grid E.grid_pos E.outer_grid
    letI : TopologicalSpace (ℝ ⊗[ℚ] V) := τ
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] V) := htopAdd
    letI : ContinuousSMul ℝ (ℝ ⊗[ℚ] V) := hsmul
    letI : T2Space (ℝ ⊗[ℚ] V) := hT2
    obtain ⟨n, ê, grid, GammaHat, hgrid, hcoords, hcoord, hshift, hEval⟩ :=
      exists_linearized_lattice E.filtration hspos E.basis E.lattice E.grid E.grid_pos hEcoords
    obtain ⟨M, hM, hfixed⟩ := exists_linearized_fixedModelRepresentation
      E hspos n ê grid GammaHat hgrid hcoords hcoord hshift hEval
    refine ⟨M, ?_⟩
    exact Exists.imp (fun _ hrepresentation => ⟨hM, hrepresentation⟩)
      (dataRepresentation_of_cover K₀ δ E (by
        intro L' _ _ D' hD'
        exact hcover L' D' (hWdata.trans hD'.symm)) M hfixed)

/-- Construct a menu piece from a point, translation, and bounded continuous observable. -/
def ofObservable {M : Menu s} {K : ℝ≥0} (i : Fin M.size)
    (g : M.G i) (x : M.G i ⧸ M.Γ i) (obs : (M.G i ⧸ M.Γ i) →ᵇ ℝ)
    (hlip : letI := (M.metric i).replaceTopology (M.compatible i)
      LipschitzWith K obs)
    (hrange : ∀ z, obs z ∈ Set.Icc (0 : ℝ) 1) : CosetPiece M K :=
  ⟨i, g, x, obs, hlip, hrange⟩


end HindmanSumsProducts.InverseBridge

namespace OAI.SourceMenuLiteral.CosetPiece

open OAI.SourceChartedMenu
open scoped NNReal BoundedContinuousFunction

variable {s : ℕ} {M : OAI.SourceChartedMenu.Menu s} {K : ℝ≥0}

/-- Shift the basepoint of a coset piece so its sequence is reindexed. -/
def shift (P : OAI.SourceMenuLiteral.CosetPiece M K) (j : ℤ) :
    OAI.SourceMenuLiteral.CosetPiece M K :=
  { P with x := P.g ^ j • P.x }

theorem shift_eval (P : OAI.SourceMenuLiteral.CosetPiece M K) (j k : ℤ) :
    (P.shift j).eval k = P.eval (k + j) := by
  simp [shift, OAI.SourceMenuLiteral.CosetPiece.eval, zpow_add, mul_smul] <;> rfl

end OAI.SourceMenuLiteral.CosetPiece
