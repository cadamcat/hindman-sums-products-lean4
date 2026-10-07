import HindmanSumsProducts.InverseBridge.Canonical

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3

/-- Every rational filtered nilmanifold has a coordinate model on a small carrier.
The finite-dimensional rational coordinate basis transports all of its data. -/
theorem exists_small_model {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) :
    ∃ (V : Type) (hV : LieRing V) (hA : LieAlgebra ℚ V),
      letI : LieRing V := hV
      letI : LieAlgebra ℚ V := hA
      ∃ W : RationalFilteredNilmanifold V s d,
        baseData W = baseData D ∧
        ∀ p, W.GeometryComplexityLE p ↔ D.GeometryComplexityLE p := by
  sorry

end HindmanSumsProducts.InverseBridge
