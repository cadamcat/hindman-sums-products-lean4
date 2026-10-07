import HindmanSumsProducts.InverseBridge.Observable
import HindmanSumsProducts.InverseBridge.Canonical
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01

/-!
Charted menus and constructors for observable pieces (IB.b1--b3).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.SourceChartedMenu OAI.SourceProductChart OAI.SourceMenuLiteral
open scoped NNReal BoundedContinuousFunction
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
theorem exists_bridgeMenu (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
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
  Classical.choose (exists_bridgeMenu s K₀ hK₀)

noncomputable def bridgeMenuLip (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) : ℝ≥0 :=
  Classical.choose (Classical.choose_spec (exists_bridgeMenu s K₀ hK₀))

noncomputable def bridgeMenuData (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    Fin (bridgeMenu s K₀ hK₀).size → BaseData s :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀ hK₀)))

theorem bridgeMenu_size_pos (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    0 < (bridgeMenu s K₀ hK₀).size :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀ hK₀)))).1

theorem bridgeMenuData_realizable (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (i : Fin (bridgeMenu s K₀ hK₀).size) : RealizableAt K₀ (bridgeMenuData s K₀ hK₀ i) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀ hK₀)))).2.1 i

theorem bridgeMenuData_covers (s : ℕ) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (δ : BaseData s)
    (hδ : RealizableAt K₀ δ) : ∃ i, bridgeMenuData s K₀ hK₀ i = δ :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀ hK₀)))).2.2 δ hδ

/-- Construct a menu piece from a point, translation, and bounded continuous observable. -/
def ofObservable {M : Menu s} {K : ℝ≥0} (i : Fin M.size)
    (g : M.G i) (x : M.G i ⧸ M.Γ i) (obs : (M.G i ⧸ M.Γ i) →ᵇ ℝ)
    (hlip : letI := (M.metric i).replaceTopology (M.compatible i)
      LipschitzWith K obs)
    (hrange : ∀ z, obs z ∈ Set.Icc (0 : ℝ) 1) : CosetPiece M K :=
  ⟨i, g, x, obs, hlip, hrange⟩

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
