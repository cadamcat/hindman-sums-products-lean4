import HindmanSumsProducts.Prediction.Results

open scoped BigOperators NNReal Topology
open Filter Classical

namespace HindmanSumsProducts.Prediction

/-- The Hilbert ultraproduct projection system from §5, lines 355–376. `base.project i l`
represents `P_{i,l}`; `represented i l f` means the family belongs to `𝒩_{i,l}`. -/
structure HilbertGapProjectionSystem (n : ℕ) where
  base : GapProjection n
  inner : (i : Fin n) → (ℕ → ℤ → ℝ) → (ℕ → ℤ → ℝ) → ℝ
  inner_cauchy_schwarz : ∀ i f g,
    |inner i f g| ≤ base.norm i f * base.norm i g
  represented : (i l : Fin n) → l < i → (ℕ → ℤ → ℝ) → Prop
  nested_subspace_inclusion : ∀ (i l l' : Fin n) (h : l < i) (h' : l' < i)
    (hll' : l < l') (v : ℕ → ℤ → ℝ),
      represented i l' h' v → represented i l h v
  project_represented : ∀ i l (h : l < i) f,
    represented i l h (base.project i l h f)
  project_pairing : ∀ i l (h : l < i) f g, represented i l h g →
    inner i (base.project i l h f) g = inner i f g
  nested_projection_identity : ∀ (i l l' : Fin n) (h : l < i) (h' : l' < i)
    (_hll' : l < l') (v : ℕ → ℤ → ℝ),
      base.norm i (base.project i l h v - base.project i l' h' v) ^ 2 =
        base.norm i (base.project i l h v) ^ 2 -
          base.norm i (base.project i l' h' v) ^ 2
  clip01_represented : ∀ i l (h : l < i) (v : ℕ → ℤ → ℝ),
    represented i l h (fun N y => max 0 (min 1 (v N y)))
  projection_norm_nonneg : ∀ i f, 0 ≤ base.norm i f

/-- The projection-distance identity in (eq:prediction-nested-spaces), §5, lines 366–376. -/
theorem nested_projection_distance_identity {n : ℕ}
    (P : HilbertGapProjectionSystem n) (i l l' : Fin n)
    (h : l < i) (h' : l' < i) (hll' : l < l') (v : ℕ → ℤ → ℝ) :
    P.base.norm i (P.base.project i l h v - P.base.project i l' h' v) ^ 2 =
      P.base.norm i (P.base.project i l h v) ^ 2 -
        P.base.norm i (P.base.project i l' h' v) ^ 2 :=
  P.nested_projection_identity i l l' h h' hll' v

/-- Existence of the Hilbert ultraproduct and its nested closed nilsequence subspaces for the
OAI harmonic pivot laws. The ultrafilter is arbitrary nonprincipal. -/
theorem hilbert_gap_projection_system {n : ℕ} (A : Parameters n)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    Nonempty (HilbertGapProjectionSystem n) := by
  sorry

/-- Fine projection norm `‖P_{i,l}v‖₂`. -/
def fineProjectionNorm {n : ℕ} (P : HilbertGapProjectionSystem n)
    (i l : Fin n) (h : l < i) (v : ℕ → ℤ → ℝ) : ℝ :=
  P.base.norm i (P.base.project i l h v)

/-- Projection-energy coloring data before the Ramsey selection. `energy` is the squared norm of
`P_{i,l}F_{T∪{i},a,c}`; `coarseApproximation` records density of represented families in the
closed nilsequence subspace. -/
structure EnergySelectionContext (M r : ℕ) (As : Finset ℚ) where
  dense : DenseModelFamily M r
  projections : HilbertGapProjectionSystem M
  energy : (B : Block M) → (l : Fin M) →
    (∀ t ∈ B.2.val, t < l) → l < B.1 →
      (a : ℚ) → a ∈ As → Fin r → ℝ
  energy_range : ∀ B l hT hl a ha c,
    0 ≤ energy B l hT hl a ha c ∧ energy B l hT hl a ha c ≤ 1
  -- GAP: spell out that `energy` is the squared projection norm and that coarse projection
  -- approximants are finite combinations of the representing families from §5, lines 398–419.
  energy_is_projection_energy : Prop
  coarseApproximation : Prop

/-- A family of master-scale energy data indexed by the master count. -/
structure MasterEnergyFamily (r : ℕ) (As : Finset ℚ) where
  context : ∀ M : ℕ, EnergySelectionContext M r As
  context_valid : ∀ M,
    (context M).energy_is_projection_energy ∧ (context M).coarseApproximation

/-- Interleaving and selected coarse models produced by the energy argument. -/
structure EnergySelectionOutput (n : ℕ) {M r : ℕ} {As : Finset ℚ}
    (E : EnergySelectionContext M r As) (eps : ℝ) (hn : 0 < n) where
  padding : Fin n → Fin M
  principal : Fin n → Fin M
  padding_before_principal : ∀ u, padding u < principal u
  principal_before_next_padding : ∀ u (hnext : u.val + 1 < n),
    principal u < padding ⟨u.val + 1, hnext⟩
  first_padding_before_all_principals : ∀ u,
    padding ⟨0, hn⟩ < principal u
  models : Fin n → DenseModelFamily M r
  models_range : ∀ (u : Fin n) (N : ℕ) (B : Block M) (a : ℚ)
    (c : Fin r) (y : ℤ), 0 ≤ models u N B a c y ∧ models u N B a c y ≤ 1
  represented_at_coarse_scale : ∀ (u : Fin n) (B : Block M),
    B.1 = principal u → (∀ t ∈ B.2.val, t < padding u) →
      ∀ (a : ℚ), a ∈ As → ∀ (c : Fin r),
        E.projections.represented (principal u) (padding u)
          (padding_before_principal u) (fun N y => models u N B a c y)
  coarse_projection_error : ∀ (u : Fin n) (B : Block M),
    B.1 = principal u → (∀ t ∈ B.2.val, t < padding u) →
      ∀ (a : ℚ), a ∈ As → ∀ (c : Fin r),
        E.projections.base.norm (principal u)
          ((fun N y => models u N B a c y) -
            E.projections.base.project (principal u) (padding u)
              (padding_before_principal u) (fun N y => E.dense N B a c y)) ≤ eps
  fine_projection_error : ∀ (u : Fin n) (B : Block M),
    B.1 = principal u → (∀ t ∈ B.2.val, t < padding ⟨0, hn⟩) →
      ∀ (a : ℚ), a ∈ As → ∀ (c : Fin r),
        E.projections.base.norm (principal u)
          (E.projections.base.project (principal u) (padding ⟨0, hn⟩)
            (first_padding_before_all_principals u)
            (fun N y => E.dense N B a c y - models u N B a c y)) ≤ 2 * eps
  complexity_bounded : Prop

/-- Ramsey selection of gap energies, Lemma `lem:energy-selection`, §5, lines 378–430.
The chosen master count depends only on the requested chain length, number of colors, finite scale
list size, and `eps`; model complexity may depend on the selected count. -/
theorem energy_selection {n r : ℕ} (hn : 0 < n) (As : Finset ℚ) (eps : ℝ) (heps : 0 < eps)
    (E : MasterEnergyFamily r As) :
    ∃ M : ℕ, Nonempty (EnergySelectionOutput n (E.context M) eps hn) := by
  sorry

/-- The local subgroup-cube comparison data in §5, lines 518–578. Its constants depend on the
cube dimension and `J₀`, but not on the number of cells. -/
structure SubgroupCubeComparison (d J0 : ℕ) where
  shortCube : ℕ → ℝ
  periodizedCube : ℕ → ℝ
  subgroupNorm : ℕ → ℝ
  boundaryError : ℕ → ℝ
  boundaryConstant : ℝ
  boundaryConstant_nonneg : 0 ≤ boundaryConstant
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  boundary_small : ∀ ε > 0, ∀ᶠ N in atTop,
    boundaryError N ≤ boundaryConstant / J0 + ε
  short_to_periodized : ∀ ε > 0, ∀ᶠ N in atTop,
    |shortCube N - periodizedCube N| ≤ boundaryError N
  cauchy_schwarz_cube_bound : ∀ N,
    |periodizedCube N| ≤ constant * subgroupNorm N

/-- The `2^d`-fold weighted Cauchy–Schwarz passage to a subgroup `U^{2^d}` norm and its
`O_d(J₀⁻¹)` periodization error, §5, lines 518–578. -/
theorem short_cube_to_subgroup_norm (d : ℕ) (J0 : ℕ) (hJ0 : 0 < J0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε > 0, ∀ᶠ N in atTop,
      ∃ S : SubgroupCubeComparison d J0,
        S.constant ≤ C * (J0 : ℝ) ^ (2 ^ d) ∧
        S.boundaryConstant ≤ C ∧
        |S.shortCube N| ≤ S.constant * S.subgroupNorm N + C / J0 + ε := by
  sorry

/-- Finite cell decomposition for the global `U^t` norm in (eq:prediction-cyclic-interval).
The moment identity is exactly the cellwise decomposition of the global cube mean. -/
structure FiniteCellGowersData (t : ℕ) where
  Cell : Type
  [cellFintype : Fintype Cell]
  [cellDecidableEq : DecidableEq Cell]
  weight : Cell → ℝ
  weight_nonneg : ∀ C, 0 ≤ weight C
  weight_sum_one : ∑ C, weight C = 1
  localNorm : Cell → ℝ
  localNorm_nonneg : ∀ C, 0 ≤ localNorm C
  localNorm_le_one : ∀ C, localNorm C ≤ 1
  globalNorm : ℝ
  globalNorm_nonneg : 0 ≤ globalNorm
  moment_identity : globalNorm ^ (2 ^ t) =
    ∑ C, weight C * localNorm C ^ (2 ^ t)

attribute [instance] FiniteCellGowersData.cellFintype
  FiniteCellGowersData.cellDecidableEq

/-- The cells with local `U^t` norm at least `δ/2` have total probability at least
`δ^(2^t)/2`, as used in §5, lines 644–652. -/
theorem global_gowers_norm_large_cells {t : ℕ} (S : FiniteCellGowersData t)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hglobal : δ ≤ S.globalNorm) :
    δ ^ (2 ^ t) / 2 ≤
      ∑ C, S.weight C * (if δ / 2 ≤ S.localNorm C then 1 else 0) := by
  sorry

/-- A piecewise nilsequence with positive Hilbert pairing forces the fine orthogonal projection
to have at least that norm. This is the final orthogonality/Cauchy–Schwarz step in §5, lines
667–674. -/
theorem projection_lower_bound_of_correlator {n : ℕ}
    (P : HilbertGapProjectionSystem n) (i l : Fin n) (hl : l < i)
    (h : ℕ → ℤ → ℝ) (V : ℕ → ℤ → ℝ) (c : ℝ)
    (hc : 0 < c) (hVrep : P.represented i l hl V)
    (hVnorm : P.base.norm i V ≤ 1) (hcor : c ≤ P.inner i h V) :
    c ≤ fineProjectionNorm P i l hl h := by
  sorry

/-- Cyclic-to-interval comparison from (eq:prediction-cyclic-interval), §5, lines 601–642. The
estimate concerns powers of the norms (the normalized cube means). -/
theorem cyclic_to_interval_cube_mean (t q K : ℕ) [NeZero q]
    (hq : 0 < q) (hK : 0 < K)
    (v : ZMod q → ℝ) :
    |intervalCubeMean t (K * q) (fun z => v (z : ZMod q)) -
      (∑ x : ZMod q, ∑ a : Fin t → ZMod q,
        ∏ ω : Finset (Fin t), v (x + ∑ j ∈ ω, a j)) /
        ((Fintype.card (ZMod q) : ℝ) ^ (t + 1))| ≤
      (t + 1 : ℝ) ^ 3 / K := by
  sorry

/-- From subgroup cubes to a fine nilsequence projection, Lemma `lem:subgroup-inverse`,
§5, lines 491–683. `κ` is independent of the master count, gap, cutoff, and cell probabilities. -/
theorem subgroup_cube_to_fine_projection (d J0 : ℕ) (hJ0 : 0 < J0)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℕ, 2 * (2 ^ d) - 2 ≤ s →
      ∀ {n : ℕ} (A : Parameters n) (P : HilbertGapProjectionSystem n)
        (B : Block n) (l : Fin n) (hl : l < B.1)
        (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite),
        ∀ (h : ℕ → ℤ → ℝ), (∀ N y, |h N y| ≤ 1) →
        ∀ D : ∀ N, DualTest B (divisorWeight A N B),
          (∀ N, (D N).dimension = d ∧ (D N).J0 = J0 ∧ (D N).gap = l) →
          fineProjectionNorm P B.1 l hl h < κ →
          UltrafilterUpperBound U
            (fun N => |DualTest.cubeAverage A N B (D N) (h N)|)
            (γ + (2 : ℝ) * d / J0) := by
  sorry

end HindmanSumsProducts.Prediction
