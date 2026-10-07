import OAI.Combinatorics.Progressions.Estimates.AxisCompression

/-!
Canonical finite base models for the inverse-theorem bridge.

The code in this file follows IB.c1--c4 in
`research/blueprint/INVERSE-BRIDGE.md`.  `BaseData` records the rational Lie
bracket, all filtered layer bases in the ambient coordinates, and the lattice
grid.  Padding rows by zero makes the record independent of the individual
rank indices.
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators NNReal

/-- Finite coordinate data attached to a rational filtered nilmanifold. -/
structure BaseData (s : ℕ) where
  d : ℕ
  bracket : Fin d → Fin d → Fin d → ℚ
  rank : Fin (s + 1) → ℕ
  rows : Fin (s + 1) → Fin d → Fin d → ℚ
  grid : ℕ

/-- The finite shadow of a rational filtered nilmanifold. -/
noncomputable def baseData {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) : BaseData s where
  d := d
  bracket := lieStructureConstants D.basis
  rank := fun i => Module.finrank ℚ (D.filtration.layer (i.val + 1))
  rows := fun i j k =>
    if hj : j.val < Module.finrank ℚ (D.filtration.layer (i.val + 1)) then
      D.basis.repr (D.layerBasis i ⟨j.val, hj⟩) k
    else 0
  grid := D.grid

/-- Bounded geometry complexity admits only finitely many finite shadows. -/
theorem baseData_finite (s : ℕ) (p : ℝ) :
    {δ : BaseData s | ∃ (L : Type*) (hL : LieRing L) (hA : LieAlgebra ℚ L),
      letI : LieRing L := hL
      letI : LieAlgebra ℚ L := hA
      ∃ D : RationalFilteredNilmanifold L s δ.d,
        D.GeometryComplexityLE p ∧ baseData D = δ}.Finite := by
  sorry

/-- A finite datum is realizable when it is the shadow of an OAI base model. -/
def Realizable {s : ℕ} (δ : BaseData s) : Prop :=
  ∃ (L : Type*) (hL : LieRing L) (hA : LieAlgebra ℚ L),
    letI : LieRing L := hL
    letI : LieAlgebra ℚ L := hA
    ∃ D : RationalFilteredNilmanifold L s δ.d, baseData D = δ

/-- Equal finite data determine a filtered Lie isomorphism matching the chosen bases. -/
theorem exists_dataEquiv {s d : ℕ} {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s d)
    (h : baseData D = baseData E) :
    ∃ φ : L ≃ₗ⁅ℚ⁆ M,
      (∀ i, φ (D.basis i) = E.basis i) ∧
      ∀ k a, a ∈ D.filtration.layer k ↔ φ a ∈ E.filtration.layer k := by
  sorry

/-- A canonical coordinate sublattice, with its coordinate grid divisible by
the original grid and contained in the original lattice.  This is IB.c3. -/
theorem exists_canonical_lattice {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) :
    ∃ B : ℕ, 0 < B ∧ D.grid ∣ B ∧
      ∃ Λ : Subgroup D.filtration.Group,
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧ Λ ≤ D.lattice := by
  sorry

/-- Pull a bounded niltest back to a canonical finite-index coordinate model,
rotate its observable, and take its real part.  The orbit identity is the
interface consumed by the linearization and menu construction (IB.c4). -/
theorem transport_to_canonical {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s d) (hDE : baseData D = baseData E)
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.normBound ≤ 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ (π : E.Space → D.Space)
      (p : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      (letI := E.metricSpace
       letI := D.metricSpace
       LipschitzWith (coordinateLipschitzBound d d 1) π) ∧
      (∀ n : ℤ, π (E.integerOrbitPoint p n) = D.integerOrbitPoint T.orbit n) ∧
      ∃ H : E.Space → ℝ,
        (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) ∧
        (letI := E.metricSpace
         LipschitzWith (T.lipBound * coordinateLipschitzBound d d 1 / 2) H) ∧
        ∀ n : ℤ, H (E.integerOrbitPoint p n) =
          (1 + (u * T.eval (fun _ => n)).re) / 2 := by
  sorry

end HindmanSumsProducts.InverseBridge
