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
theorem exists_bridgeMenu (s : ℕ) (K₀ : ℝ) :
    ∃ (M : Menu (2 * s)) (K : ℝ≥0)
      (data : Fin M.size → BaseData s),
      0 < M.size ∧ (∀ i, RealizableAt K₀ (data i)) ∧
        ∀ δ, RealizableAt K₀ δ → ∃ i, data i = δ := by
  sorry

/-- A charted menu selected uniformly from the finite canonical list. -/
noncomputable def bridgeMenu (s : ℕ) (K₀ : ℝ) : Menu (2 * s) :=
  Classical.choose (exists_bridgeMenu s K₀)

noncomputable def bridgeMenuLip (s : ℕ) (K₀ : ℝ) : ℝ≥0 :=
  Classical.choose (Classical.choose_spec (exists_bridgeMenu s K₀))

noncomputable def bridgeMenuData (s : ℕ) (K₀ : ℝ) :
    Fin (bridgeMenu s K₀).size → BaseData s :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀)))

theorem bridgeMenu_size_pos (s : ℕ) (K₀ : ℝ) : 0 < (bridgeMenu s K₀).size :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀)))).1

theorem bridgeMenuData_realizable (s : ℕ) (K₀ : ℝ) (i : Fin (bridgeMenu s K₀).size) :
    RealizableAt K₀ (bridgeMenuData s K₀ i) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀)))).2.1 i

theorem bridgeMenuData_covers (s : ℕ) (K₀ : ℝ) (δ : BaseData s)
    (hδ : RealizableAt K₀ δ) : ∃ i, bridgeMenuData s K₀ i = δ :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_bridgeMenu s K₀)))).2.2 δ hδ

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
