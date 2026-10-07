import OAI.Combinatorics.Progressions.Estimates.AxisCompression


/-!
Polynomial-orbit linearization nodes IB.a1--a5 and IB.a7--a8.

The actual construction is the derivative semidirect extension and its weight
filtration.  The interfaces are kept here so the observable, menu, and assembly
files can use them without duplicating the algebra.
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3
open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

/-- The adapted Lie algebra of one-variable, degree-weighted vector polynomials. -/
noncomputable abbrev Poly (F : NilpotentLieFiltration L s) :=
  F.adaptedLieSubalgebra (fun _ : Unit => 1)

/-- The coordinate derivative on vector polynomials. -/
noncomputable def polyDeriv :
    LieDerivation ℚ (VectorPolynomial Unit ℚ L) (VectorPolynomial Unit ℚ L) :=
  Lie.Derivation.ofDerivation L (MvPolynomial.pderiv ())

/-- Coefficient formula for the derivative, including zero and constant terms. -/
theorem polyDeriv_coefficients (Q : VectorPolynomial Unit ℚ L) (j : ℕ) :
    VectorPolynomial.coefficients (polyDeriv Q) (Finsupp.single () j) =
      ((j + 1 : ℚ)) •
        VectorPolynomial.coefficients Q (Finsupp.single () (j + 1)) := by
  simpa [polyDeriv, Lie.Derivation.ofDerivation_apply] using
    OAI.Erdos3.VectorPolynomial.coefficients_pderiv () Q (Finsupp.single () j)

/-- The derivative preserves adapted polynomials, hence restricts to their Lie algebra. -/
theorem exists_polyDeriv_restriction (F : NilpotentLieFiltration L s) :
    ∃ D : LieDerivation ℚ (Poly F) (Poly F),
      ∀ Q, (D Q : VectorPolynomial Unit ℚ L) = polyDeriv Q := by
  classical
  let D : LieDerivation ℚ (Poly F) (Poly F) :=
    ⟨F.adaptedDirectionalDerivative (fun _ : Unit => 1), by
      intro Q R
      have h := F.adaptedDirectionalDerivative_lie (fun _ : Unit => 1) Q R
      simpa [lie_skew, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h⟩
  refine ⟨D, ?_⟩
  intro Q
  change (F.adaptedDirectionalDerivative (fun _ : Unit => 1) Q : VectorPolynomial Unit ℚ L) =
    polyDeriv Q
  rw [F.adaptedDirectionalDerivative_coe]
  simp [VectorPolynomial.directionalDerivative, polyDeriv,
    Lie.Derivation.ofDerivation_apply]

noncomputable def hD (F : NilpotentLieFiltration L s) :
    LieDerivation ℚ (Poly F) (Poly F) := Classical.choose (exists_polyDeriv_restriction F)

theorem hD_apply (F : NilpotentLieFiltration L s) (Q : Poly F) :
    (hD F Q : VectorPolynomial Unit ℚ L) = polyDeriv Q :=
  (Classical.choose_spec (exists_polyDeriv_restriction F)) Q

/-- A synonym for the abelian rational Lie algebra used for translation. -/
abbrev Line := ℚ

local instance lineLieRing : LieRing Line := LieRing.ofAssociativeRing
local instance lineLieAlgebra : LieAlgebra ℚ Line := LieAlgebra.ofAssociativeAlgebra

/-- Scalar multiples of the polynomial derivative give the translation action. -/
theorem exists_shiftAction (F : NilpotentLieFiltration L s) :
    ∃ ψ : Line →ₗ⁅ℚ⁆ LieDerivation ℚ (Poly F) (Poly F),
      ∀ a, ψ a = a • hD F := by
  let ψ : Line →ₗ⁅ℚ⁆ LieDerivation ℚ (Poly F) (Poly F) := {
    toLinearMap := LinearMap.toSpanSingleton ℚ (LieDerivation ℚ (Poly F) (Poly F)) (hD F)
    map_lie' := by
      intro a b
      have hab : ⁅a, b⁆ = 0 := by
        change a * b - b * a = 0
        ring
      rw [hab]
      simp [lie_smul, smul_lie, lie_self]
  }
  refine ⟨ψ, ?_⟩
  intro a
  change LinearMap.toSpanSingleton ℚ (LieDerivation ℚ (Poly F) (Poly F)) (hD F) a =
    a • hD F
  rfl

noncomputable def shiftAction (F : NilpotentLieFiltration L s) :
    Line →ₗ⁅ℚ⁆ LieDerivation ℚ (Poly F) (Poly F) :=
  Classical.choose (exists_shiftAction F)

theorem shiftAction_apply (F : NilpotentLieFiltration L s) (a : Line) :
    shiftAction F a = a • hD F :=
  Classical.choose_spec (exists_shiftAction F) a

theorem shiftAction_coefficients (F : NilpotentLieFiltration L s) (a : Line)
    (Q : Poly F) :
    (shiftAction F a Q : VectorPolynomial Unit ℚ L) =
      VectorPolynomial.directionalDerivative (fun _ : Unit => (a : ℚ)) Q.val := by
  rw [shiftAction_apply]
  simp [hD_apply, VectorPolynomial.directionalDerivative, polyDeriv,
    Lie.Derivation.ofDerivation_apply]

/-- The Lie algebra obtained by adjoining the translation direction. -/
abbrev Lin (F : NilpotentLieFiltration L s) := Poly F ⋊⁅shiftAction F⁆ Line

noncomputable def Dhat (F : NilpotentLieFiltration L s) : Lin F :=
  LieAlgebra.SemiDirectSum.inr _ (1 : Line)

noncomputable def rLin (F : NilpotentLieFiltration L s) : Lin F →ₗ⁅ℚ⁆ Line :=
  LieAlgebra.SemiDirectSum.projr _

/-- Evaluate the polynomial component at an integer. -/
noncomputable def evLin (F : NilpotentLieFiltration L s) (m : ℤ) : Lin F →ₗ[ℚ] L :=
  (VectorPolynomial.eval (fun _ : Unit => (m : ℚ))).comp
    ((Poly F).incl.toLinearMap.comp (LieAlgebra.SemiDirectSum.projl _))

private theorem shiftPolynomialLayer_unit_iff (F : NilpotentLieFiltration L s) (k : ℕ)
    (Q : VectorPolynomial Unit ℚ L) :
    Q ∈ F.shiftPolynomialLayer k ↔
      ∀ j : ℕ, VectorPolynomial.coefficients Q (Finsupp.single () j) ∈
        F.layer ((k + j + 1) / 2) := by
  change (∀ α : Unit →₀ ℕ,
      VectorPolynomial.coefficients Q α ∈
        F.layer ((k + Finsupp.weight (fun _ : Unit => 1) α + 1) / 2)) ↔ _
  have hweight (α : Unit →₀ ℕ) :
      Finsupp.weight (fun _ : Unit => 1) α = α () := by
    rw [show (fun _ : Unit => 1) = Pi.single () (1 : ℕ) by
      funext u; cases u; simp]
    exact Finsupp.weight_single_one_apply () α
  constructor
  · intro h j
    simpa [hweight] using h (Finsupp.single () j)
  · intro h α
    have hα : α = Finsupp.single () (α ()) := by
      exact Finsupp.ext (fun u => by cases u; simp)
    rw [hα]
    simpa [hweight] using h (α ())

/-- The weight filtration of degree `2*s` on the semidirect extension. -/
theorem exists_weightFiltration (F : NilpotentLieFiltration L s) (hs : 0 < s) :
    ∃ W : NilpotentLieFiltration (Lin F) (2 * s),
      ∀ (k : ℕ) (x : Lin F), x ∈ W.layer k ↔
        ((2 ≤ k → rLin F x = 0) ∧
          ∀ j : ℕ,
            VectorPolynomial.coefficients
              ((LieAlgebra.SemiDirectSum.projl (shiftAction F) x).val :
                VectorPolynomial Unit ℚ L) (Finsupp.single () j) ∈
              F.layer ((k + j + 1) / 2)) := by
  classical
  let WLayer : ℕ → Submodule ℚ (Lin F) := fun k => {
    carrier := {x | x.left.val ∈ F.shiftPolynomialLayer k ∧ (2 ≤ k → rLin F x = 0)}
    zero_mem' := by
      constructor
      · exact (F.shiftPolynomialLayer k).zero_mem
      · intro hk
        simp [rLin]
    add_mem' := by
      intro x y hx hy
      constructor
      · exact (F.shiftPolynomialLayer k).add_mem hx.1 hy.1
      · intro hk
        have hxr : rLin F x = 0 := hx.2 hk
        have hyr : rLin F y = 0 := hy.2 hk
        change x.right = 0 at hxr
        change y.right = 0 at hyr
        simp [rLin, hxr, hyr]
    smul_mem' := by
      intro c x hx
      constructor
      · exact (F.shiftPolynomialLayer k).smul_mem c hx.1
      · intro hk
        have hxr : rLin F x = 0 := hx.2 hk
        change x.right = 0 at hxr
        simp [rLin, hxr]
  }
  have hshift (a : Line) (k : ℕ) (p : Poly F)
      (hp : p.val ∈ F.shiftPolynomialLayer k) :
      (shiftAction F a p).val ∈ F.shiftPolynomialLayer (k + 1) := by
    rw [shiftAction_coefficients]
    exact F.directionalDerivative_mem_shiftPolynomialLayer (fun _ : Unit => (a : ℚ)) hp
  let W : NilpotentLieFiltration (Lin F) (2 * s) := {
    layer := WLayer
    antitone := by
      intro i j hij x hx
      constructor
      · exact F.shiftPolynomialLayer_antitone hij hx.1
      · intro hj
        exact hx.2 (le_trans (by omega) hij)
    one_eq_top := by
      apply top_unique
      intro x _
      change x.left.val ∈ F.shiftPolynomialLayer 1 ∧ (2 ≤ 1 → rLin F x = 0)
      exact ⟨F.adapted_mem_shiftPolynomialLayer_one x.left, by omega⟩
    lie_mem := by
      intro i j x y hx hy
      change x.left.val ∈ F.shiftPolynomialLayer i ∧ (2 ≤ i → rLin F x = 0) at hx
      change y.left.val ∈ F.shiftPolynomialLayer j ∧ (2 ≤ j → rLin F y = 0) at hy
      have hleft :
          (⁅x, y⁆ : Lin F).left.val ∈ F.shiftPolynomialLayer (i + j) := by
        have hxy : ⁅x.left.val, y.left.val⁆ ∈ F.shiftPolynomialLayer (i + j) :=
          F.shiftPolynomialLayer_lie hx.1 hy.1
        have hAct1 : (shiftAction F x.right y.left).val ∈
            F.shiftPolynomialLayer (i + j) := by
          by_cases hi : 2 ≤ i
          · have hxr : x.right = 0 := by simpa [rLin] using hx.2 hi
            rw [hxr]
            simp
          · exact F.shiftPolynomialLayer_antitone (by omega) (hshift x.right j y.left hy.1)
        have hAct2 : (shiftAction F y.right x.left).val ∈
            F.shiftPolynomialLayer (i + j) := by
          by_cases hj : 2 ≤ j
          · have hyr : y.right = 0 := by simpa [rLin] using hy.2 hj
            rw [hyr]
            simp
          · exact F.shiftPolynomialLayer_antitone (by omega) (hshift y.right i x.left hx.1)
        have hformula :
            (⁅x, y⁆ : Lin F).left.val =
              ⁅x.left.val, y.left.val⁆ + (shiftAction F x.right y.left).val -
                (shiftAction F y.right x.left).val := rfl
        rw [hformula]
        exact (F.shiftPolynomialLayer (i + j)).sub_mem
          ((F.shiftPolynomialLayer (i + j)).add_mem hxy hAct1) hAct2
      have hright : rLin F ⁅x, y⁆ = 0 := by
        change ⁅x.right, y.right⁆ = 0
        change x.right * y.right - y.right * x.right = 0
        ring
      change (⁅x, y⁆ : Lin F).left.val ∈ F.shiftPolynomialLayer (i + j) ∧
        (2 ≤ i + j → rLin F ⁅x, y⁆ = 0)
      exact ⟨hleft, fun _ => hright⟩
    terminal := by
      apply bot_unique
      intro x hx
      change x.left.val ∈ F.shiftPolynomialLayer (2 * s + 1) ∧
        (2 ≤ 2 * s + 1 → rLin F x = 0) at hx
      have hleftval : x.left.val = 0 := by
        simpa only [F.shiftPolynomialLayer_terminal, Submodule.mem_bot] using hx.1
      have hleft : x.left = 0 := Subtype.ext hleftval
      have hright : rLin F x = 0 := hx.2 (by omega)
      have hright' : x.right = 0 := by simpa [rLin] using hright
      change x = 0
      apply (LieAlgebra.SemiDirectSum.toProdl (shiftAction F)).injective
      exact Prod.ext hleft hright'
  }
  refine ⟨W, ?_⟩
  intro k x
  change (x.left.val ∈ F.shiftPolynomialLayer k ∧ (2 ≤ k → rLin F x = 0)) ↔ _
  rw [shiftPolynomialLayer_unit_iff F k x.left.val]
  constructor
  · rintro ⟨hcoeff, hr⟩
    exact ⟨hr, hcoeff⟩
  · rintro ⟨hr, hcoeff⟩
    exact ⟨hcoeff, hr⟩

noncomputable def weightFiltration (F : NilpotentLieFiltration L s) (hs : 0 < s) :
    NilpotentLieFiltration (Lin F) (2 * s) :=
  Classical.choose (exists_weightFiltration F hs)

theorem weightFiltration_layer (F : NilpotentLieFiltration L s)
    (hs : 0 < s) (k : ℕ) (x : Lin F) : x ∈ (weightFiltration F hs).layer k ↔
      ((2 ≤ k → rLin F x = 0) ∧
        ∀ j : ℕ,
          VectorPolynomial.coefficients
            ((LieAlgebra.SemiDirectSum.projl (shiftAction F) x).val :
              VectorPolynomial Unit ℚ L) (Finsupp.single () j) ∈
            F.layer ((k + j + 1) / 2)) :=
  Classical.choose_spec (exists_weightFiltration F hs) k x

/-- A finite basis and coordinate-height bounds for the linearized algebra. -/
theorem exists_linearized_basis (F : NilpotentLieFiltration L s)
    {d : ℕ} (e₀ : Basis (Fin d) ℚ L) :
    ∃ n : ℕ, ∃ e : Basis (Fin n) ℚ (Lin F),
      ∃ H den : ℕ, 0 < den ∧
        (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) ∧
        (∀ i j, IntegralVector
          ((den : ℚ) •
            (e₀.equivFun
              (VectorPolynomial.coefficients
                (LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val
                (Finsupp.single () j))))) := by
  sorry

/-- The stable integral grid on the linearized algebra maps its kernel into the
original lattice, while the translation coordinate lies in the grid. -/
theorem exists_linearized_lattice (F : NilpotentLieFiltration L s) (hs : 0 < s)
    {d : ℕ} (e : Basis (Fin d) ℚ L) (Λ : Subgroup F.Group) (BΛ : ℕ)
    (hBΛ : 0 < BΛ)
    (hΛ : bchSubgroupCoordinates e Λ = scaledIntegerGrid BΛ) :
    ∃ (n : ℕ) (ê : Basis (Fin n) ℚ (Lin F)) (B : ℕ)
      (GammaHat : Subgroup ((weightFiltration F hs).Group)),
      0 < B ∧ bchSubgroupCoordinates ê GammaHat = scaledIntegerGrid B ∧
      (∀ γ ∈ GammaHat, ∃ z : ℤ, (rLin F γ.coord : ℚ) = B * z) ∧
      (∀ z : ℤ, (⟨(B * z : ℚ) • Dhat F⟩ : (weightFiltration F hs).Group) ∈ GammaHat) ∧
      (∀ γ ∈ GammaHat, rLin F γ.coord = 0 →
        ∀ m : ℤ, (⟨evLin F m γ.coord⟩ : F.Group) ∈ Λ) := by
  sorry

/-- Taylor's finite exponential formula for translation of a polynomial. -/
theorem polynomial_translation_taylor (S : ℕ) (Q : VectorPolynomial Unit ℚ L)
    (hQ : ∀ j, S < j →
      VectorPolynomial.coefficients Q (Finsupp.single () j) = 0) (h : ℚ) :
    (∑ j ∈ Finset.range (S + 1),
      ((h ^ j / (j.factorial : ℚ)) • (polyDeriv^[j] Q))) =
        VectorPolynomial.translate (fun _ : Unit => h) Q := by
  sorry

/-- Base changes of the polynomial evaluation and translation coordinate. -/
noncomputable def evLinReal (F : NilpotentLieFiltration L s) (m : ℤ) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] (ℝ ⊗[ℚ] L) := (evLin F m).baseChange ℝ

noncomputable def rLinReal (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] (ℝ ⊗[ℚ] Line) := (rLin F).baseChange ℝ

/-- Every adapted real polynomial log has a basepoint in the kernel of the
translation coordinate whose evaluations are the given polynomial values. -/
theorem exists_linearized_basepoint (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P) :
    ∃ x : ℝ ⊗[ℚ] Lin F, rLinReal F x = 0 ∧
      ∀ m : ℤ, evLinReal F m x =
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ)) P := by
  sorry

end HindmanSumsProducts.InverseBridge
