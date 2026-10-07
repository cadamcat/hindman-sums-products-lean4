import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import HindmanSumsProducts.InverseBridge.Assembly.AdjointExp

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
  rw [polyDeriv, Lie.Derivation.ofDerivation_apply]
  change VectorPolynomial.coefficients
      ((MvPolynomial.pderiv ()).toLinearMap.rTensor L Q)
      (Finsupp.single () j) = _
  rw [VectorPolynomial.coefficients_pderiv]
  simp

/-- The derivative preserves adapted polynomials, hence restricts to their Lie algebra. -/
theorem exists_polyDeriv_restriction (F : NilpotentLieFiltration L s) :
    ∃ D : LieDerivation ℚ (Poly F) (Poly F),
      ∀ Q, (D Q : VectorPolynomial Unit ℚ L) = polyDeriv Q := by
  refine ⟨{
    toLinearMap := {
      toFun := fun Q => ⟨polyDeriv Q.1, ?_⟩
      map_add' := by
        intro Q R
        apply Subtype.ext
        simp
      map_smul' := by
        intro a Q
        apply Subtype.ext
        simp
    }
    leibniz' := ?_
  }, ?_⟩
  · change polyDeriv Q.1 ∈ F.adaptedSubmodule (fun _ : Unit => 1)
    rw [F.mem_adaptedSubmodule]
    rw [F.adapted_iff_coefficients]
    intro α
    change VectorPolynomial.coefficients
        ((MvPolynomial.pderiv ()).toLinearMap.rTensor L Q.1) α ∈ _
    rw [VectorPolynomial.coefficients_pderiv]
    have hQadapt : F.Adapted (fun _ : Unit => 1) Q.1 := by
      apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) Q.1).mp
      change Q.1 ∈ F.adaptedSubmodule (fun _ : Unit => 1)
      exact Q.2
    have hQ := (F.adapted_iff_coefficients (fun _ : Unit => 1) Q.1).mp hQadapt
    have hcoeff := hQ (α + Finsupp.single () 1)
    have hweight : Finsupp.weight (fun _ : Unit => 1) (α + Finsupp.single () 1) =
        Finsupp.weight (fun _ : Unit => 1) α + 1 := by
      simp [Finsupp.weight]
    rw [hweight] at hcoeff
    exact F.antitone (Nat.le_succ _) ((F.layer
      (Finsupp.weight (fun _ : Unit => 1) α + 1)).smul_mem _ hcoeff)
  · intro Q R
    apply Subtype.ext
    change polyDeriv ⁅Q.1, R.1⁆ = ⁅Q.1, polyDeriv R.1⁆ - ⁅R.1, polyDeriv Q.1⁆
    exact (polyDeriv).leibniz' Q.1 R.1
  · intro Q
    rfl

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
  refine ⟨{
    toFun := fun a => a • hD F
    map_add' := by intro a b; exact add_smul a b (hD F)
    map_smul' := by
      intro c a
      change (c * a) • hD F = c • (a • hD F)
      exact (smul_smul c a (hD F)).symm
    map_lie' := by
      intro a b
      have hab : ⁅a, b⁆ = (0 : Line) := by
        rw [LieRing.of_associative_ring_bracket]
        ring
      rw [hab]
      simp
  }, fun _ => rfl⟩

noncomputable def shiftAction (F : NilpotentLieFiltration L s) :
    Line →ₗ⁅ℚ⁆ LieDerivation ℚ (Poly F) (Poly F) :=
  Classical.choose (exists_shiftAction F)

private theorem directionalDerivative_unit (a : ℚ) (Q : VectorPolynomial Unit ℚ L) :
    VectorPolynomial.directionalDerivative (fun _ : Unit => a) Q =
      a • ((MvPolynomial.pderiv ()).toLinearMap.rTensor L Q) := by
  apply VectorPolynomial.coefficients.injective
  ext α
  simp [VectorPolynomial.coefficients_directionalDerivative,
    VectorPolynomial.coefficients_pderiv]

theorem shiftAction_apply (F : NilpotentLieFiltration L s) (a : Line) (Q : Poly F) :
    (shiftAction F a Q : VectorPolynomial Unit ℚ L) =
      VectorPolynomial.directionalDerivative (fun _ : Unit => a) Q := by
  have hψ : shiftAction F a = a • hD F :=
    Classical.choose_spec (exists_shiftAction F) a
  rw [hψ]
  change a • (hD F Q : VectorPolynomial Unit ℚ L) = _
  rw [hD_apply, polyDeriv, Lie.Derivation.ofDerivation_apply]
  exact (directionalDerivative_unit a Q.val).symm

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

private def linearizedLayer (F : NilpotentLieFiltration L s) (k : ℕ) :
    Submodule ℚ (Lin F) where
  carrier := {x | (2 ≤ k → rLin F x = 0) ∧
    ∀ j : ℕ,
      VectorPolynomial.coefficients
        ((LieAlgebra.SemiDirectSum.projl (shiftAction F) x).val :
          VectorPolynomial Unit ℚ L) (Finsupp.single () j) ∈ F.layer ((k + j + 1) / 2)}
  zero_mem' := by
    constructor
    · intro _
      change (0 : Line) = 0
      rfl
    · intro j
      simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro hk
      have hx' : x.right = 0 := by simpa [rLin] using hx.1 hk
      have hy' : y.right = 0 := by simpa [rLin] using hy.1 hk
      change x.right + y.right = 0
      rw [hx', hy']
      simp
    · intro j
      simpa using (F.layer ((k + j + 1) / 2)).add_mem (hx.2 j) (hy.2 j)
  smul_mem' := by
    intro a x hx
    constructor
    · intro hk
      have hx' : x.right = 0 := by simpa [rLin] using hx.1 hk
      change a • x.right = 0
      rw [hx']
      simp
    · intro j
      simpa using (F.layer ((k + j + 1) / 2)).smul_mem a (hx.2 j)

private theorem unitShiftPolynomialLayer_iff (F : NilpotentLieFiltration L s)
    (k : ℕ) (Q : VectorPolynomial Unit ℚ L) :
    Q ∈ F.shiftPolynomialLayer (σ := Unit) k ↔
      ∀ j : ℕ, VectorPolynomial.coefficients Q (Finsupp.single () j) ∈
        F.layer ((k + j + 1) / 2) := by
  change (∀ α : Unit →₀ ℕ,
      VectorPolynomial.coefficients Q α ∈
        F.layer ((k + Finsupp.weight (fun _ : Unit => 1) α + 1) / 2)) ↔ _
  constructor
  · intro hQ j
    simpa [Finsupp.weight_single] using hQ (Finsupp.single () j)
  · intro hQ α
    have hα : α = Finsupp.single () (α ()) := by
      ext u
      simp
    rw [hα]
    simpa [Finsupp.weight_single] using hQ (α ())

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
  refine ⟨{
    layer := linearizedLayer F
    antitone := by
      intro i j hij x hx
      constructor
      · intro hi
        exact hx.1 (le_trans hi hij)
      · intro n
        exact F.antitone (by omega) (hx.2 n)
    one_eq_top := by
      apply top_unique
      intro x _
      constructor
      · intro h
        omega
      · intro j
        let Q := LieAlgebra.SemiDirectSum.projl (shiftAction F) x
        have hmem : Q.val ∈ F.adaptedSubmodule (fun _ : Unit => 1) := by
          change Q.val ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
          exact Q.property
        have hQ : F.Adapted (fun _ : Unit => 1) Q.val :=
          (F.mem_adaptedSubmodule (fun _ : Unit => 1) Q.val).mp hmem
        have hc : VectorPolynomial.coefficients Q.val (Finsupp.single () j) ∈
            F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () j)) :=
          ((F.adapted_iff_coefficients (fun _ : Unit => 1) Q.val).mp hQ)
            (Finsupp.single () j)
        by_cases hj : j = 0
        · subst j
          norm_num
          rw [F.one_eq_top]
          exact Submodule.mem_top
        · have hidx : (1 + j + 1) / 2 ≤ j := by omega
          have hc' : VectorPolynomial.coefficients Q.val (Finsupp.single () j) ∈ F.layer j := by
            simpa [Finsupp.weight_single] using hc
          exact F.antitone hidx hc'
    lie_mem := by
      intro i j x y hx hy
      constructor
      · intro _
        rw [LieHom.map_lie]
        rw [LieRing.of_associative_ring_bracket]
        ring
      · intro n
        have hp : x.left.val ∈ F.shiftPolynomialLayer (σ := Unit) i := by
          apply (unitShiftPolynomialLayer_iff F i x.left.val).2
          intro d
          simpa using hx.2 d
        have hq : y.left.val ∈ F.shiftPolynomialLayer (σ := Unit) j := by
          apply (unitShiftPolynomialLayer_iff F j y.left.val).2
          intro d
          simpa using hy.2 d
        have hbase := F.shiftPolynomialLayer_lie hp hq
        have hact₁ : (shiftAction F x.right y.left : VectorPolynomial Unit ℚ L) ∈
            F.shiftPolynomialLayer (σ := Unit) (i + j) := by
          by_cases hi : 2 ≤ i
          · have hr : x.right = 0 := by simpa [rLin] using hx.1 hi
            rw [shiftAction_apply, hr]
            simpa [VectorPolynomial.directionalDerivative] using
              (F.shiftPolynomialLayer (σ := Unit) (i + j)).zero_mem
          · have hi' : i ≤ 1 := by omega
            rw [shiftAction_apply]
            exact F.shiftPolynomialLayer_antitone (by omega)
              (F.directionalDerivative_mem_shiftPolynomialLayer
                (fun _ : Unit => x.right) hq)
        have hact₂ : (shiftAction F y.right x.left : VectorPolynomial Unit ℚ L) ∈
            F.shiftPolynomialLayer (σ := Unit) (i + j) := by
          by_cases hj : 2 ≤ j
          · have hr : y.right = 0 := by simpa [rLin] using hy.1 hj
            rw [shiftAction_apply, hr]
            simpa [VectorPolynomial.directionalDerivative] using
              (F.shiftPolynomialLayer (σ := Unit) (i + j)).zero_mem
          · have hj' : j ≤ 1 := by omega
            rw [shiftAction_apply]
            exact F.shiftPolynomialLayer_antitone (by omega)
              (F.directionalDerivative_mem_shiftPolynomialLayer
                (fun _ : Unit => y.right) hp)
        have hpoly : (⁅x.left, y.left⁆ + shiftAction F x.right y.left -
            shiftAction F y.right x.left : Poly F).val ∈
              F.shiftPolynomialLayer (σ := Unit) (i + j) :=
          (F.shiftPolynomialLayer (σ := Unit) (i + j)).sub_mem
            ((F.shiftPolynomialLayer (σ := Unit) (i + j)).add_mem hbase hact₁) hact₂
        simpa [LieAlgebra.SemiDirectSum.lie_eq_mk] using
          (unitShiftPolynomialLayer_iff F (i + j)
            ((LieAlgebra.SemiDirectSum.projl (shiftAction F) ⁅x, y⁆).val)).mp
            (by simpa [LieAlgebra.SemiDirectSum.lie_eq_mk] using hpoly) n
    terminal := by
      apply bot_unique
      intro x hx
      change x = 0
      have hline : rLin F x = 0 := hx.1 (by omega)
      have hcoeff (j : ℕ) :
          VectorPolynomial.coefficients
            ((LieAlgebra.SemiDirectSum.projl (shiftAction F) x).val :
              VectorPolynomial Unit ℚ L) (Finsupp.single () j) = 0 := by
        have hmem := F.antitone (show s + 1 ≤ (2 * s + 1 + j + 1) / 2 by omega) (hx.2 j)
        simpa only [F.terminal, Submodule.mem_bot] using hmem
      have hpoly : ((LieAlgebra.SemiDirectSum.projl (shiftAction F) x).val :
          VectorPolynomial Unit ℚ L) = 0 := by
        apply VectorPolynomial.coefficients.injective
        apply Finsupp.ext
        intro α
        have hα : α = Finsupp.single () (α ()) := by
          ext u
          simp
        rw [hα]
        exact hcoeff (α ())
      apply LieAlgebra.SemiDirectSum.ext
      · exact Subtype.ext hpoly
      · simpa [rLin] using hline
  }, ?_⟩
  intro k x
  rfl

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

private noncomputable def polyCoeffWindowMap (F : NilpotentLieFiltration L s) :
    Poly F →ₗ[ℚ] (Fin (s + 1) → L) where
  toFun Q := fun j =>
    VectorPolynomial.coefficients (Q : VectorPolynomial Unit ℚ L) (Finsupp.single () j.val)
  map_add' Q R := by
    ext j
    simp
  map_smul' a Q := by
    ext j
    simp

private theorem polyCoeffWindowMap_injective (F : NilpotentLieFiltration L s) :
    Function.Injective (polyCoeffWindowMap F) := by
  intro Q R hQR
  apply Subtype.ext
  apply VectorPolynomial.coefficients.injective
  ext α
  have hαeq : α = Finsupp.single () (α ()) := by
    ext u
    simp
  by_cases hα : α () ≤ s
  · rw [hαeq]
    have hc := congrFun hQR (⟨α (), by omega⟩ : Fin (s + 1))
    simpa [polyCoeffWindowMap] using hc
  · have hQadapt : F.Adapted (fun _ : Unit => 1) Q.val := by
      apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) Q.val).mp
      change Q.val ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
      exact Q.property
    have hRadapt : F.Adapted (fun _ : Unit => 1) R.val := by
      apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) R.val).mp
      change R.val ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
      exact R.property
    rw [hαeq]
    have hQzero : VectorPolynomial.coefficients Q.val
        (Finsupp.single () (α ())) = 0 := by
      exact F.adapted_degreeLE (fun _ : Unit => 1) hQadapt
        (Finsupp.single () (α ()))
        (by simpa [Finsupp.weight_single] using (show s < α () by omega))
    have hRzero : VectorPolynomial.coefficients R.val
        (Finsupp.single () (α ())) = 0 := by
      exact F.adapted_degreeLE (fun _ : Unit => 1) hRadapt
        (Finsupp.single () (α ()))
        (by simpa [Finsupp.weight_single] using (show s < α () by omega))
    rw [hQzero, hRzero]

private theorem poly_finiteDimensional (F : NilpotentLieFiltration L s)
    {d : ℕ} (e₀ : Basis (Fin d) ℚ L) : FiniteDimensional ℚ (Poly F) := by
  letI : FiniteDimensional ℚ L := e₀.finiteDimensional_of_finite
  exact FiniteDimensional.of_injective (polyCoeffWindowMap F) (polyCoeffWindowMap_injective F)

private theorem lin_finiteDimensional (F : NilpotentLieFiltration L s)
    {d : ℕ} (e₀ : Basis (Fin d) ℚ L) : FiniteDimensional ℚ (Lin F) := by
  letI : FiniteDimensional ℚ (Poly F) := poly_finiteDimensional F e₀
  letI : FiniteDimensional ℚ Line := by
    change FiniteDimensional ℚ ℚ
    infer_instance
  exact FiniteDimensional.of_injective
    (LieAlgebra.SemiDirectSum.toProdl (shiftAction F)).toLinearMap
    (LieAlgebra.SemiDirectSum.toProdl (shiftAction F)).injective

private def finSumUnitEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit where
  toFun i := if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr ()
  invFun
    | Sum.inl i => ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    | Sum.inr _ => ⟨n, Nat.lt_succ_self n⟩
  left_inv i := by
    apply Fin.ext
    by_cases h : i.val < n
    · simp [h]
    · have hi : i.val = n := by omega
      simp [h, hi]
  right_inv x := by
    cases x with
    | inl i => simp [i.isLt]
    | inr _ => simp

private noncomputable def linearizedBasis (F : NilpotentLieFiltration L s)
    [FiniteDimensional ℚ (Poly F)] :
    Basis (Fin (finrank ℚ (Poly F) + 1)) ℚ (Lin F) := by
  let b := (Module.finBasis ℚ (Poly F)).prod (Basis.singleton Unit ℚ)
  let c := b.map (LieAlgebra.SemiDirectSum.toProdl (shiftAction F)).symm
  exact c.reindex (finSumUnitEquiv (finrank ℚ (Poly F))).symm

private theorem linearizedBasis_last_repr (F : NilpotentLieFiltration L s)
    [FiniteDimensional ℚ (Poly F)] (x : Lin F) :
    (linearizedBasis F).repr x (Fin.last (finrank ℚ (Poly F))) = rLin F x := by
  have hidx : finSumUnitEquiv (finrank ℚ (Poly F))
      (Fin.last (finrank ℚ (Poly F))) = Sum.inr () := by
    simp [finSumUnitEquiv]
  rw [linearizedBasis, Basis.repr_reindex_apply]
  simp only [Equiv.symm_symm]
  rw [hidx]
  change ((Module.finBasis ℚ (Poly F)).prod (Basis.singleton Unit ℚ)).repr
    ((LieAlgebra.SemiDirectSum.toProdl (shiftAction F)) x) (Sum.inr ()) = rLin F x
  simp [Basis.prod_repr_inr, Basis.singleton_repr, rLin,
    LieAlgebra.SemiDirectSum.toProdl, LieAlgebra.SemiDirectSum.toProd]

private theorem linearizedBasis_last_eq_Dhat (F : NilpotentLieFiltration L s)
    [FiniteDimensional ℚ (Poly F)] :
    linearizedBasis F (Fin.last (finrank ℚ (Poly F))) = Dhat F := by
  have hidx : finSumUnitEquiv (finrank ℚ (Poly F))
      (Fin.last (finrank ℚ (Poly F))) = Sum.inr () := by
    simp [finSumUnitEquiv]
  rw [linearizedBasis, Basis.reindex_apply]
  simp only [Equiv.symm_symm]
  rw [hidx]
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    simp [Basis.map_apply, Basis.prod_apply_inr_fst, Basis.singleton_apply,
      LieAlgebra.SemiDirectSum.toProdl, LieAlgebra.SemiDirectSum.toProd, Dhat]
  · simp [Basis.map_apply, Basis.prod_apply_inr_snd, Basis.singleton_apply,
      LieAlgebra.SemiDirectSum.toProdl, LieAlgebra.SemiDirectSum.toProd, Dhat]

/-- A finite basis and coordinate-height bounds for the linearized algebra. -/
private theorem exists_linearized_basis_aux (F : NilpotentLieFiltration L s)
    [FiniteDimensional ℚ (Poly F)]
    {d : ℕ} (e₀ : Basis (Fin d) ℚ L) :
    ∃ H den : ℕ, 0 < den ∧
        (∀ i j k, RationalHeightLE
          (lieStructureConstants (linearizedBasis F) i j k) H) ∧
        (∀ i j, IntegralVector
          ((den : ℚ) •
            (e₀.equivFun
              (VectorPolynomial.coefficients
                (LieAlgebra.SemiDirectSum.projl (shiftAction F) (linearizedBasis F i)).val
                (Finsupp.single () j))))) := by
  classical
  let n := finrank ℚ (Poly F) + 1
  let e : Basis (Fin n) ℚ (Lin F) := linearizedBasis F
  let H := max 1 (Finset.univ.sup fun ijk : Fin n × (Fin n × Fin n) =>
    ⌈Real.exp (rationalLogHeight (lieStructureConstants e ijk.1 ijk.2.1 ijk.2.2))⌉₊)
  let A : Matrix (Fin n) (Fin (s + 1) × Fin d) ℚ := fun i jk =>
    (e₀.equivFun (VectorPolynomial.coefficients
      ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
        VectorPolynomial Unit ℚ L) (Finsupp.single () jk.1.val))) jk.2
  let den := matrixDenominator A
  have hheight : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H := by
    intro i j k
    have hs := Finset.le_sup (f := fun ijk : Fin n × (Fin n × Fin n) =>
      ⌈Real.exp (rationalLogHeight (lieStructureConstants e ijk.1 ijk.2.1 ijk.2.2))⌉₊)
      (Finset.mem_univ (i, (j, k)))
    have hq : RationalHeightLE (lieStructureConstants e i j k)
        ⌈Real.exp (rationalLogHeight (lieStructureConstants e i j k))⌉₊ :=
      rationalHeightLE_ceil_exp le_rfl
    exact hq.mono (le_trans hs (Nat.le_max_right 1 _))
  have hden : 0 < den := by
    dsimp [den]
    exact matrixDenominator_pos A
  have hcoord (i : Fin n) (j : Fin (s + 1)) :
      IntegralVector ((den : ℚ) • e₀.equivFun
        (VectorPolynomial.coefficients
          ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
            VectorPolynomial Unit ℚ L) (Finsupp.single () j.val))) := by
    let C := clearedMatrix A
    refine ⟨fun k => C i (j, k), ?_⟩
    intro k
    have hc := congrArg (fun M : Matrix (Fin n) (Fin (s + 1) × Fin d) ℚ => M i (j, k))
      (clearedMatrix_cast A)
    have hc' : (den : ℚ) * A i (j, k) = (C i (j, k) : ℚ) := by
      simpa [den, C, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using hc.symm
    change (den : ℚ) * (e₀.equivFun
      (VectorPolynomial.coefficients
        ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
          VectorPolynomial Unit ℚ L) (Finsupp.single () j.val))) k = _
    simpa [A, C] using hc'
  refine ⟨H, den, hden, hheight, ?_⟩
  intro i j
  by_cases hj : j ≤ s
  · let jf : Fin (s + 1) := ⟨j, by omega⟩
    simpa [jf] using hcoord i jf
  · have hzero : VectorPolynomial.coefficients
        ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
          VectorPolynomial Unit ℚ L) (Finsupp.single () j) = 0 := by
      have hmem :
          ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
            VectorPolynomial Unit ℚ L) ∈ F.adaptedSubmodule (fun _ : Unit => 1) := by
        change ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
          VectorPolynomial Unit ℚ L) ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
        exact (LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).property
      have hadapt := (F.mem_adaptedSubmodule (fun _ : Unit => 1) _).mp hmem
      have hdeg := F.adapted_degreeLE (fun _ : Unit => 1) hadapt (Finsupp.single () j)
        (by simpa [Finsupp.weight_single] using (show s < j by omega))
      exact hdeg
    refine ⟨fun _ => 0, ?_⟩
    intro k
    change (den : ℚ) * (e₀.equivFun
      (VectorPolynomial.coefficients
        ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (e i)).val :
          VectorPolynomial Unit ℚ L) (Finsupp.single () j))) k = 0
    rw [hzero]
    simp

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
  letI : FiniteDimensional ℚ (Poly F) := poly_finiteDimensional F e₀
  obtain ⟨H, den, hden, hheight, hcoord⟩ := exists_linearized_basis_aux F e₀
  exact ⟨finrank ℚ (Poly F) + 1, linearizedBasis F, H, den, hden, hheight, hcoord⟩

private noncomputable def scalarCoordinatePolynomial {d : ℕ}
    (e₀ : Basis (Fin d) ℚ L) (Q : VectorPolynomial Unit ℚ L) (k : Fin d) :
    MvPolynomial Unit ℚ :=
  ∑ α ∈ (VectorPolynomial.coefficients Q).support,
    MvPolynomial.monomial α ((e₀.equivFun (VectorPolynomial.coefficients Q α)) k)

private theorem scalarCoordinatePolynomial_eval {d : ℕ}
    (e₀ : Basis (Fin d) ℚ L) (Q : VectorPolynomial Unit ℚ L) (k : Fin d)
    (m : ℚ) :
    MvPolynomial.eval (fun _ : Unit => m) (scalarCoordinatePolynomial e₀ Q k) =
      (e₀.equivFun (VectorPolynomial.eval (fun _ : Unit => m) Q)) k := by
  classical
  unfold scalarCoordinatePolynomial
  conv_rhs => rw [← VectorPolynomial.sum_monomial_coefficients Q]
  simp [VectorPolynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

private theorem scalarCoordinatePolynomial_degree (F : NilpotentLieFiltration L s)
    {d : ℕ} (e₀ : Basis (Fin d) ℚ L) (Q : Poly F) (k : Fin d) :
    (scalarCoordinatePolynomial e₀ (Q : VectorPolynomial Unit ℚ L) k).totalDegree ≤ s := by
  classical
  have hQ : F.Adapted (fun _ : Unit => 1) (Q : VectorPolynomial Unit ℚ L) := by
    apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) _).mp
    change (Q : VectorPolynomial Unit ℚ L) ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
    exact Q.property
  unfold scalarCoordinatePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α hα
  apply (MvPolynomial.totalDegree_monomial_le α _).trans
  have hcoeff : VectorPolynomial.coefficients (Q : VectorPolynomial Unit ℚ L) α ≠ 0 :=
    Finsupp.mem_support_iff.mp hα
  have hw : Finsupp.weight (fun _ : Unit => 1) α ≤ s := by
    by_contra h
    have hzero := F.adapted_degreeLE (fun _ : Unit => 1) hQ α (by omega)
    exact hcoeff hzero
  have hweight : Finsupp.weight (fun _ : Unit => 1) α = α () := by
    simp [Finsupp.weight_eq_sum]
  rw [hweight] at hw
  have hαeq : α = Finsupp.single () (α ()) := by
    ext u
    simp
  rw [hαeq]
  change Finsupp.sum (Finsupp.single () (α ())) (fun _ c => c) ≤ s
  simpa using hw

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
  classical
  letI : FiniteDimensional ℚ (Poly F) := poly_finiteDimensional F e
  let n₀ := finrank ℚ (Poly F)
  let n := n₀ + 1
  let ê : Basis (Fin n) ℚ (Lin F) := linearizedBasis F
  have hLastRepr (x : Lin F) : ê.equivFun x (Fin.last n₀) = rLin F x := by
    simpa [ê, Basis.equivFun] using linearizedBasis_last_repr F x
  have hLastBasis : ê (Fin.last n₀) = Dhat F := by
    simpa [ê] using linearizedBasis_last_eq_Dhat F
  obtain ⟨H, den, hden, hheight, hcoords⟩ := exists_linearized_basis_aux F e
  let P : Fin n × Fin d → MvPolynomial Unit ℚ := fun ik =>
    scalarCoordinatePolynomial e
      ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (ê ik.1)).val) ik.2
  let D := polynomialFamilyDenominator P
  have hD : 0 < D := polynomialFamilyDenominator_pos P
  have hPdegree : ∀ ik : Fin n × Fin d, (P ik).totalDegree ≤ s := by
    intro ik
    exact scalarCoordinatePolynomial_degree F e
      (LieAlgebra.SemiDirectSum.projl (shiftAction F) (ê ik.1)) ik.2
  have hInput (m : ℤ) : (fun _ : Unit => (m : ℚ)) ∈ denominatorGrid 1 := by
    refine ⟨fun _ => m, ?_⟩
    intro u
    change (1 : ℚ) * (m : ℚ) = (m : ℚ)
    ring
  have hFamilyEval (m : ℤ) :
      (fun ik : Fin n × Fin d => MvPolynomial.eval (fun _ : Unit => (m : ℚ)) (P ik)) ∈
        denominatorGrid D := by
    have h := polynomial_family_rational_values_grid P 1 s hPdegree
      (fun _ : Unit => (m : ℚ)) (hInput m)
    simpa [D] using h
  have hEvalBasis (m : ℤ) (i : Fin n) :
      ∃ z : Fin d → ℤ, ∀ k,
        (D : ℚ) * (e.equivFun (evLin F m (ê i))) k = (z k : ℚ) := by
    obtain ⟨z, hz⟩ := hFamilyEval m
    refine ⟨fun k => z (i, k), ?_⟩
    intro k
    have hk := hz (i, k)
    have hev := scalarCoordinatePolynomial_eval e
      ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (ê i)).val) k (m : ℚ)
    have heval : evLin F m (ê i) = VectorPolynomial.eval
        (fun _ : Unit => (m : ℚ))
        ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (ê i)).val) := rfl
    calc
      (D : ℚ) * (e.equivFun (evLin F m (ê i))) k =
          (D : ℚ) * (e.equivFun (VectorPolynomial.eval
            (fun _ : Unit => (m : ℚ))
            ((LieAlgebra.SemiDirectSum.projl (shiftAction F) (ê i)).val))) k := by rw [heval]
      _ = (D : ℚ) * MvPolynomial.eval (fun _ : Unit => (m : ℚ)) (P (i, k)) := by
        simpa [P] using (congrArg (fun q => (D : ℚ) * q) hev).symm
      _ = (z (i, k) : ℚ) := hk
  let W := weightFiltration F hs
  let hnil : LieModule.lowerCentralSeries ℚ (Lin F) (Lin F) (2 * s) = ⊥ :=
    W.lowerCentralSeries_eq_bot
  let l := D * BΛ
  have hl : 0 < l := Nat.mul_pos hD hBΛ
  obtain ⟨B, hB, hdiv, _, hstable⟩ :=
    exists_bch_stable_integral_grid ê hnil l hl hheight
  let GammaHat : Subgroup W.Group := coordinateGridBCHSubgroup ê B hnil hstable
  have hGammaCoords : bchSubgroupCoordinates ê GammaHat = scaledIntegerGrid B :=
    coordinateGridBCHSubgroup_coordinates ê B hnil hstable
  have hGridCoordinates {γ : W.Group} (hγ : γ ∈ GammaHat) :
      ∃ z : Fin n → ℤ, ê.equivFun γ.coord = (B : ℚ) • fun i => (z i : ℚ) := by
    have h := (bchSubgroupCoordinates_repr ê GammaHat γ).mpr hγ
    rw [hGammaCoords] at h
    exact h
  refine ⟨n, ê, B, GammaHat, hB, hGammaCoords, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨z, hz⟩ := hGridCoordinates hγ
    refine ⟨z (Fin.last n₀), ?_⟩
    calc
      (rLin F γ.coord : ℚ) = ê.equivFun γ.coord (Fin.last n₀) := (hLastRepr γ.coord).symm
      _ = (B : ℚ) * (z (Fin.last n₀) : ℚ) := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun hz (Fin.last n₀)
  · intro z
    let g : W.Group := ⟨(B * z : ℚ) • Dhat F⟩
    have hgcoord : ê.equivFun g.coord ∈ bchSubgroupCoordinates ê GammaHat := by
      rw [hGammaCoords]
      change ê.equivFun ((B * z : ℚ) • Dhat F) ∈ scaledIntegerGrid B
      refine ⟨fun i => if i = Fin.last n₀ then z else 0, ?_⟩
      ext i
      rw [map_smul, ← hLastBasis]
      by_cases hi : i = Fin.last n₀ <;> simp [hi, Pi.smul_apply, smul_eq_mul]
    exact (bchSubgroupCoordinates_repr ê GammaHat g).mp hgcoord
  · intro γ hγ _ m
    obtain ⟨z, hz⟩ := hGridCoordinates hγ
    obtain ⟨K, hK⟩ := hdiv
    have hKq : (B : ℚ) = (D : ℚ) * (BΛ : ℚ) * (K : ℚ) := by
      rw [hK]
      dsimp [l]
      push_cast
      ring
    choose v hv using hEvalBasis m
    have hEvalGamma : e.equivFun (evLin F m γ.coord) =
        ∑ i : Fin n, ((B : ℚ) * (z i : ℚ)) •
          e.equivFun (evLin F m (ê i)) := by
      have hreps (i : Fin n) : ê.repr γ.coord i = (B : ℚ) * (z i : ℚ) := by
        have hi := congrFun hz i
        simpa [Basis.equivFun, Pi.smul_apply, smul_eq_mul] using hi
      have hrepr : γ.coord = ∑ i : Fin n, ((B : ℚ) * (z i : ℚ)) • ê i := by
        rw [← ê.sum_repr γ.coord]
        apply Finset.sum_congr rfl
        intro i _
        rw [hreps i]
      calc
        _ = e.equivFun (evLin F m (∑ i : Fin n,
            ((B : ℚ) * (z i : ℚ)) • ê i)) := by rw [hrepr]
        _ = e.equivFun (∑ i : Fin n,
            ((B : ℚ) * (z i : ℚ)) • evLin F m (ê i)) := by
              congr 1
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _
              exact (evLin F m).map_smul _ _
        _ = ∑ i : Fin n, ((B : ℚ) * (z i : ℚ)) •
            e.equivFun (evLin F m (ê i)) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _
              exact e.equivFun.map_smul _ _
    have hEvalGrid : e.equivFun (evLin F m γ.coord) ∈ scaledIntegerGrid BΛ := by
      refine ⟨fun k => ∑ i : Fin n, (K : ℤ) * z i * v i k, ?_⟩
      ext k
      have hk := congrFun hEvalGamma k
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hk
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hterm : (B : ℚ) * (z i : ℚ) * (e.equivFun (evLin F m (ê i))) k =
          ((BΛ : ℚ) * ((K : ℤ) * z i * v i k : ℤ) : ℚ) := by
        rw [hKq]
        push_cast
        rw [← hv i k]
        ring
      simpa only [Int.cast_mul, Int.cast_natCast] using hterm
    have hEvalSubgroupCoords :
        e.equivFun ((⟨evLin F m γ.coord⟩ : F.Group).coord) ∈ bchSubgroupCoordinates e Λ := by
      change e.equivFun (evLin F m γ.coord) ∈ bchSubgroupCoordinates e Λ
      rw [hΛ]
      exact hEvalGrid
    exact (bchSubgroupCoordinates_repr e Λ
      (⟨evLin F m γ.coord⟩ : F.Group)).mp hEvalSubgroupCoords

/-- Taylor's finite exponential formula for translation of a polynomial. -/
private theorem scalarDirectionalDerivative_unit (h : ℚ) :
    scalarDirectionalDerivative (fun _ : Unit => h) = h • MvPolynomial.pderiv () := by
  ext P
  simp [scalarDirectionalDerivative_apply]

private theorem scalarLinearEnd_smul_pow (h : ℚ)
    (D : Module.End ℚ (MvPolynomial Unit ℚ)) (n : ℕ) :
    (h • D) ^ n = h ^ n • D ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (h • D) ^ (n + 1) = (h • D) ^ n * (h • D) := by rw [pow_succ]
        _ = (h ^ n • D ^ n) * (h • D) := by rw [ih]
        _ = h ^ n • (D ^ n * (h • D)) := by rw [smul_mul_assoc]
        _ = h ^ n • (h • (D ^ n * D)) := by rw [mul_smul_comm]
        _ = (h ^ n * h) • (D ^ n * D) := by rw [smul_smul]
        _ = h ^ (n + 1) • D ^ (n + 1) := by rw [pow_succ, pow_succ]

private theorem scalarDirectionalDerivative_unit_iterate (h : ℚ) (n : ℕ)
    (P : MvPolynomial Unit ℚ) :
    ((scalarDirectionalDerivative (fun _ : Unit => h)).toLinearMap ^ n) P =
      h ^ n • ((MvPolynomial.pderiv ()).toLinearMap ^ n) P := by
  rw [scalarDirectionalDerivative_unit h]
  exact congrArg (fun f : Module.End ℚ (MvPolynomial Unit ℚ) => f P)
    (scalarLinearEnd_smul_pow h (MvPolynomial.pderiv ()).toLinearMap n)

private theorem scalarPolynomialTranslationTaylor (S : ℕ) (P : MvPolynomial Unit ℚ)
    (hP : ∀ j, S < j → P.coeff (Finsupp.single () j) = 0) (h : ℚ) :
    (∑ j ∈ Finset.range (S + 1),
      ((h ^ j / (j.factorial : ℚ)) • ((MvPolynomial.pderiv ()).toLinearMap ^ j) P)) =
        polynomialTranslate (fun _ : Unit => h) P := by
  classical
  let x : Unit → ℚ := fun _ => h
  have hsupportLE : P ∈ weightedSupportLE (fun _ : Unit => 1) S := by
    intro α hα
    have hαeq : α = Finsupp.single () (α ()) := by
      ext u
      simp
    by_contra hnot
    have hdegree : S < α () := by
      rw [hαeq] at hnot
      have hnot' : ¬ α () ≤ S := by
        simpa [Finsupp.weight_single] using hnot
      omega
    have hz := hP (α ()) hdegree
    rw [← hαeq] at hz
    exact (Finsupp.mem_support_iff.mp hα) hz
  have hnil : ((scalarDirectionalDerivative x).toLinearMap ^ (S + 1)) P = 0 :=
    scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport
      (fun _ : Unit => 1) (by intro; norm_num) x hsupportLE
  let path := polynomialTranslationPath (-x) P
  have hpathSupport : path.support ⊆ Finset.range (S + 1) := by
    exact polynomialTranslationPath_neg_support_of_nilpotent x hnil
  have hEval : path.eval 1 = polynomialTranslate (fun _ : Unit => h) P := by
    have hh := polynomialTranslationPath_eval (-x) 1 P
    simpa [path, x] using hh
  have hEvalSum : path.eval 1 = ∑ j ∈ Finset.range (S + 1), path.coeff j := by
    calc
      path.eval 1 = ∑ j ∈ path.support, path.coeff j := by
        change Polynomial.eval₂ (RingHom.id (MvPolynomial Unit ℚ)) 1 path = _
        rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        simp
      _ = ∑ j ∈ Finset.range (S + 1), path.coeff j := by
        apply Finset.sum_subset hpathSupport
        intro j hj hjn
        simp [Polynomial.notMem_support_iff.mp hjn]
  have hcoeff (j : ℕ) : path.coeff j =
      ((h ^ j / (j.factorial : ℚ)) • ((MvPolynomial.pderiv ()).toLinearMap ^ j) P) := by
    dsimp [path]
    rw [polynomialTranslationPath_neg_coeff]
    rw [scalarDirectionalDerivative_unit_iterate]
    simp only [smul_smul, div_eq_mul_inv]
    congr 1
    ring
  calc
    _ = ∑ j ∈ Finset.range (S + 1), path.coeff j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff]
    _ = path.eval 1 := hEvalSum.symm
    _ = polynomialTranslate (fun _ : Unit => h) P := hEval

private theorem polyDeriv_iterate_tmul (n : ℕ) (P : MvPolynomial Unit ℚ) (v : L) :
    polyDeriv^[n] (P ⊗ₜ[ℚ] v) =
      (((MvPolynomial.pderiv ()).toLinearMap ^ n) P) ⊗ₜ[ℚ] v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, polyDeriv, Lie.Derivation.ofDerivation_apply,
        LinearMap.rTensor_tmul]
      congr 1
      rw [Module.End.iterate_succ', LinearMap.comp_apply]

private theorem polyDeriv_iterate_add (n : ℕ) (P Q : VectorPolynomial Unit ℚ L) :
    polyDeriv^[n] (P + Q) = polyDeriv^[n] P + polyDeriv^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]

private theorem polyDeriv_iterate_smul (n : ℕ) (a : ℚ)
    (P : VectorPolynomial Unit ℚ L) :
    polyDeriv^[n] (a • P) = a • polyDeriv^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, map_smul]

private theorem polyDeriv_iterate_finsupp_sum (n : ℕ) (f : (Unit →₀ ℕ) →₀ L) :
    polyDeriv^[n] ((f.sum fun α v => VectorPolynomial.monomial α v) :
      VectorPolynomial Unit ℚ L) =
      f.sum fun α v => polyDeriv^[n] (VectorPolynomial.monomial α v) := by
  classical
  change polyDeriv^[n] (∑ α ∈ f.support, VectorPolynomial.monomial α (f α)) =
    ∑ α ∈ f.support, polyDeriv^[n] (VectorPolynomial.monomial α (f α))
  exact polyDeriv_iterate_sum n f.support (fun α => VectorPolynomial.monomial α (f α))
where
  polyDeriv_iterate_sum (n : ℕ) (s : Finset (Unit →₀ ℕ))
      (f : (Unit →₀ ℕ) → VectorPolynomial Unit ℚ L) :
      polyDeriv^[n] (∑ α ∈ s, f α) = ∑ α ∈ s, polyDeriv^[n] (f α) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert α s hα ih =>
        simp only [Finset.sum_insert hα, polyDeriv_iterate_add, ih]

private theorem polynomialTranslationTaylor_monomial (S : ℕ)
    (α : Unit →₀ ℕ) (v : L) (hα : α () ≤ S) (h : ℚ) :
    (∑ j ∈ Finset.range (S + 1),
      ((h ^ j / (j.factorial : ℚ)) •
        (polyDeriv^[j] (VectorPolynomial.monomial α v)))) =
      VectorPolynomial.translate (fun _ : Unit => h) (VectorPolynomial.monomial α v) := by
  have hTaylor := scalarPolynomialTranslationTaylor S (MvPolynomial.monomial α (1 : ℚ))
    (by
      intro j hj
      by_cases hne : α = Finsupp.single () j
      · have : α () = j := by simpa using congrArg (fun β : Unit →₀ ℕ => β ()) hne
        omega
      · simp [MvPolynomial.coeff_monomial, hne]) h
  calc
    _ = ∑ j ∈ Finset.range (S + 1),
        (((h ^ j / (j.factorial : ℚ)) •
          (((MvPolynomial.pderiv ()).toLinearMap ^ j) (MvPolynomial.monomial α (1 : ℚ)))) ⊗ₜ[ℚ] v) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [VectorPolynomial.monomial, polyDeriv_iterate_tmul,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    _ = ((∑ j ∈ Finset.range (S + 1),
        (h ^ j / (j.factorial : ℚ)) •
          (((MvPolynomial.pderiv ()).toLinearMap ^ j) (MvPolynomial.monomial α (1 : ℚ)))) ⊗ₜ[ℚ] v) := by
      rw [TensorProduct.sum_tmul]
    _ = (polynomialTranslate (fun _ : Unit => h) (MvPolynomial.monomial α (1 : ℚ))) ⊗ₜ[ℚ] v := by
      rw [hTaylor]
    _ = VectorPolynomial.translate (fun _ : Unit => h) (VectorPolynomial.monomial α v) := rfl

theorem polynomial_translation_taylor (S : ℕ) (Q : VectorPolynomial Unit ℚ L)
    (hQ : ∀ j, S < j →
      VectorPolynomial.coefficients Q (Finsupp.single () j) = 0) (h : ℚ) :
    (∑ j ∈ Finset.range (S + 1),
      ((h ^ j / (j.factorial : ℚ)) • (polyDeriv^[j] Q))) =
        VectorPolynomial.translate (fun _ : Unit => h) Q := by
  classical
  let f := VectorPolynomial.coefficients Q
  have hdecomp : f.sum (fun α v => VectorPolynomial.monomial α v) = Q := by
    simpa [f] using VectorPolynomial.sum_monomial_coefficients Q
  have hIter (j : ℕ) : polyDeriv^[j] Q =
      f.sum (fun α v => polyDeriv^[j] (VectorPolynomial.monomial α v)) := by
    rw [← hdecomp, polyDeriv_iterate_finsupp_sum]
  have hdegree (α : Unit →₀ ℕ) (hα : α ∈ f.support) :
      α () ≤ S := by
    have hcoeff : f α ≠ 0 := by simpa [f] using (Finsupp.mem_support_iff.mp hα)
    by_contra hnot
    have hαeq : α = Finsupp.single () (α ()) := by
      ext u
      simp
    have hz := hQ (α ()) (by omega)
    have hz' : f α = 0 := by
      change VectorPolynomial.coefficients Q α = 0
      rw [hαeq]
      exact hz
    exact hcoeff hz'
  calc
    _ = ∑ j ∈ Finset.range (S + 1),
        ∑ α ∈ f.support,
          ((h ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (VectorPolynomial.monomial α (f α))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hIter j]
      change (h ^ j / (j.factorial : ℚ)) •
          (∑ α ∈ f.support, polyDeriv^[j] (VectorPolynomial.monomial α (f α))) = _
      rw [Finset.smul_sum]
    _ = ∑ α ∈ f.support,
        ∑ j ∈ Finset.range (S + 1),
          ((h ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (VectorPolynomial.monomial α (f α))) := by
      rw [Finset.sum_comm]
    _ = ∑ α ∈ f.support,
        VectorPolynomial.translate (fun _ : Unit => h)
          (VectorPolynomial.monomial α (f α)) := by
      apply Finset.sum_congr rfl
      intro α hα
      exact polynomialTranslationTaylor_monomial S α (f α)
        (hdegree α hα) h
    _ = VectorPolynomial.translate (fun _ : Unit => h)
        (f.sum (fun α v => VectorPolynomial.monomial α v)) := by
      change (∑ α ∈ f.support, VectorPolynomial.translate (fun _ : Unit => h)
        (VectorPolynomial.monomial α (f α))) =
        VectorPolynomial.translate (fun _ : Unit => h)
          (∑ α ∈ f.support, VectorPolynomial.monomial α (f α))
      rw [map_sum]
    _ = VectorPolynomial.translate (fun _ : Unit => h) Q := by rw [hdecomp]

/-- Base changes of the polynomial evaluation and translation coordinate. -/
noncomputable def evLinReal (F : NilpotentLieFiltration L s) (m : ℤ) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] (ℝ ⊗[ℚ] L) := (evLin F m).baseChange ℝ

noncomputable def rLinReal (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] (ℝ ⊗[ℚ] Line) := (rLin F).baseChange ℝ

noncomputable def realInl (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Poly F) →ₗ[ℝ] (ℝ ⊗[ℚ] Lin F) :=
  (LieAlgebra.SemiDirectSum.inl (shiftAction F)).toLinearMap.baseChange ℝ

private noncomputable def adaptedMonomialLift (F : NilpotentLieFiltration L s)
    (α : Unit →₀ ℕ) :
    F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α) →ₗ[ℚ] Poly F where
  toFun x := ⟨VectorPolynomial.monomial α (x : L), by
    change VectorPolynomial.monomial α (x : L) ∈
      F.adaptedLieSubalgebra (fun _ : Unit => 1)
    exact F.monomial_mem_adaptedSubmodule (fun _ : Unit => 1) α x.property⟩
  map_add' x y := by
    apply Subtype.ext
    change MvPolynomial.monomial α (1 : ℚ) ⊗ₜ[ℚ] ((x : L) + (y : L)) =
      (MvPolynomial.monomial α (1 : ℚ) ⊗ₜ[ℚ] (x : L)) +
        (MvPolynomial.monomial α (1 : ℚ) ⊗ₜ[ℚ] (y : L))
    rw [TensorProduct.tmul_add]
  map_smul' a x := by
    apply Subtype.ext
    change MvPolynomial.monomial α (1 : ℚ) ⊗ₜ[ℚ] (a • (x : L)) =
      a • (MvPolynomial.monomial α (1 : ℚ) ⊗ₜ[ℚ] (x : L))
    exact TensorProduct.tmul_smul _ _ _

private theorem adaptedMonomialLift_apply (F : NilpotentLieFiltration L s)
    (α : Unit →₀ ℕ) (x : F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)) :
    (adaptedMonomialLift F α x : VectorPolynomial Unit ℚ L) =
      VectorPolynomial.monomial α (x : L) := rfl

private noncomputable def realMonomialLift (F : NilpotentLieFiltration L s)
    (α : Unit →₀ ℕ) :
    (ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)) →ₗ[ℚ]
      VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L) :=
  (F.realAdaptedPolynomialMap (fun _ : Unit => 1)).toLinearMap.comp
    (((adaptedMonomialLift F α).baseChange ℝ).restrictScalars ℚ)

private theorem realMonomialLift_coefficient (F : NilpotentLieFiltration L s)
    (α β : Unit →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)) :
    VectorPolynomial.coefficients (realMonomialLift F α x) β =
      if β = α then
        ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ x :
          ℝ ⊗[ℚ] L)
      else 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a l =>
      by_cases hβα : β = α
      · subst β
        change VectorPolynomial.coefficients
          (F.realAdaptedPolynomialMap (fun _ : Unit => 1)
            (a ⊗ₜ[ℚ] (adaptedMonomialLift F α l))) α = _
        rw [F.realAdaptedPolynomialMap_coefficient_tmul]
        rw [adaptedMonomialLift_apply, VectorPolynomial.coefficients_monomial]
        simp only [Finsupp.single_eq_same, if_true]
        exact (Submodule.coe_toBaseChange_tmul (R := ℚ) (M := L) ℝ
          (F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)) a l).symm
      · change VectorPolynomial.coefficients
          (F.realAdaptedPolynomialMap (fun _ : Unit => 1)
            (a ⊗ₜ[ℚ] (adaptedMonomialLift F α l))) β = _
        rw [F.realAdaptedPolynomialMap_coefficient_tmul]
        rw [adaptedMonomialLift_apply, VectorPolynomial.coefficients_monomial]
        simp [hβα, Submodule.coe_toBaseChange_tmul]
  | add x y hx hy =>
      have hsum (γ : Unit →₀ ℕ) :
          VectorPolynomial.coefficients (realMonomialLift F α (x + y)) γ =
            VectorPolynomial.coefficients (realMonomialLift F α x) γ +
            VectorPolynomial.coefficients (realMonomialLift F α y) γ := by
        rw [(realMonomialLift F α).map_add x y]
        exact congrArg (fun c : (Unit →₀ ℕ) →₀ (ℝ ⊗[ℚ] L) => c γ)
          ((VectorPolynomial.coefficients (σ := Unit) (R := ℚ)
            (V := ℝ ⊗[ℚ] L)).map_add _ _)
      by_cases hβα : β = α
      · subst β
        rw [hsum α, hx, hy]
        simp only [if_true]
        exact (congrArg Subtype.val
          (((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ).map_add
            x y)).symm
      · have hx0 : VectorPolynomial.coefficients (realMonomialLift F α x) β = 0 := by
          simpa [hβα] using hx
        have hy0 : VectorPolynomial.coefficients (realMonomialLift F α y) β = 0 := by
          simpa [hβα] using hy
        rw [hsum β, hx0, hy0]
        simp [hβα]

private theorem realAdaptedPolynomialMap_eval_tmul (F : NilpotentLieFiltration L s)
    (a : ℝ) (q : Poly F) (x : Unit → ℚ) :
    VectorPolynomial.eval x
        (F.realAdaptedPolynomialMap (fun _ : Unit => 1) (a ⊗ₜ[ℚ] q)) =
      a ⊗ₜ[ℚ] VectorPolynomial.eval x (q : VectorPolynomial Unit ℚ L) := by
  change VectorPolynomial.eval x
      (VectorPolynomial.realificationLieEquiv
        (a ⊗ₜ[ℚ] (q : VectorPolynomial Unit ℚ L))) = _
  exact VectorPolynomial.eval_realificationLieEquiv_tmul a
    (q : VectorPolynomial Unit ℚ L) x

/-- The realified semidirect inclusion lands in the kernel of the translation coordinate. -/
theorem rLinReal_realInl_apply (F : NilpotentLieFiltration L s)
    (x : ℝ ⊗[ℚ] Poly F) : rLinReal F (realInl F x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a q =>
      simp [realInl, rLinReal, rLin, LieAlgebra.SemiDirectSum.projr_inl_apply]
  | add x y hx hy =>
      rw [(realInl F).map_add, (rLinReal F).map_add, hx, hy]
      simp

/-- Integer evaluation on the realified semidirect inclusion is polynomial evaluation. -/
theorem evLinReal_realInl_apply (F : NilpotentLieFiltration L s) (m : ℤ)
    (x : ℝ ⊗[ℚ] Poly F) :
    evLinReal F m (realInl F x) = VectorPolynomial.eval
      (fun _ : Unit => (m : ℚ)) (F.realAdaptedPolynomialMap (fun _ : Unit => 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a q =>
      simpa [realInl, evLinReal, evLin, LieAlgebra.SemiDirectSum.projl_inl_apply] using
        (realAdaptedPolynomialMap_eval_tmul F a q
          (fun _ : Unit => (m : ℚ))).symm
  | add x y hx hy =>
      calc
        evLinReal F m (realInl F (x + y)) =
            evLinReal F m (realInl F x) + evLinReal F m (realInl F y) := by
              rw [(realInl F).map_add, (evLinReal F m).map_add]
        _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
              (F.realAdaptedPolynomialMap (fun _ : Unit => 1) x) +
            VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
              (F.realAdaptedPolynomialMap (fun _ : Unit => 1) y) := by rw [hx, hy]
        _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
              (F.realAdaptedPolynomialMap (fun _ : Unit => 1) (x + y)) := by
              rw [map_add, (VectorPolynomial.eval (fun _ : Unit => (m : ℚ))).map_add]

set_option maxHeartbeats 5000000
private theorem realAdaptedPolynomialMap_monomialSum
    (F : NilpotentLieFiltration L s)
    (f : (Unit →₀ ℕ) →₀ (ℝ ⊗[ℚ] L))
    (y : ∀ α : Unit →₀ ℕ,
      ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)) :
    F.realAdaptedPolynomialMap (fun _ : Unit => 1)
        (∑ α ∈ f.support, (adaptedMonomialLift F α).baseChange ℝ (y α)) =
      ∑ α ∈ f.support, realMonomialLift F α (y α) := by
  simp only [map_sum, realMonomialLift, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply]
  rfl

private theorem realMonomialLift_coefficients_sum
    (F : NilpotentLieFiltration L s)
    (f : (Unit →₀ ℕ) →₀ (ℝ ⊗[ℚ] L))
    (y : ∀ α : Unit →₀ ℕ,
      ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α))
    (hy : ∀ α : Unit →₀ ℕ,
      ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ
        (y α) : ℝ ⊗[ℚ] L) = f α)
    (β : Unit →₀ ℕ) :
    ∑ α ∈ f.support, VectorPolynomial.coefficients
      (realMonomialLift F α (y α)) β = f β := by
  classical
  by_cases hβ : β ∈ f.support
  · rw [Finset.sum_eq_single β]
    · rw [realMonomialLift_coefficient]
      simp [hy β]
    · intro α hα hne
      rw [realMonomialLift_coefficient]
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot hβ).elim
  · have hz : f β = 0 := by
      by_contra hne
      exact hβ (Finsupp.mem_support_iff.mpr hne)
    rw [hz]
    apply Finset.sum_eq_zero
    intro α hα
    rw [realMonomialLift_coefficient]
    have hne : β ≠ α := by
      intro heq
      subst α
      exact hβ hα
    simp [hne]

private theorem realAdaptedPolynomialMap_monomialSum_coefficients
    (F : NilpotentLieFiltration L s)
    (f : (Unit →₀ ℕ) →₀ (ℝ ⊗[ℚ] L))
    (y : ∀ α : Unit →₀ ℕ,
      ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α))
    (hy : ∀ α : Unit →₀ ℕ,
      ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ
        (y α) : ℝ ⊗[ℚ] L) = f α) :
    F.realAdaptedPolynomialMap (fun _ : Unit => 1)
        (∑ α ∈ f.support, (adaptedMonomialLift F α).baseChange ℝ (y α)) =
      (VectorPolynomial.coefficients (σ := Unit) (R := ℚ)
        (V := ℝ ⊗[ℚ] L)).symm f := by
  apply (VectorPolynomial.coefficients (σ := Unit) (R := ℚ)
    (V := ℝ ⊗[ℚ] L)).injective
  ext β
  rw [realAdaptedPolynomialMap_monomialSum, map_sum,
    LinearEquiv.apply_symm_apply]
  rw [Finset.sum_apply']
  exact realMonomialLift_coefficients_sum F f y hy β

private theorem realAdapted_coefficient_mem
    (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P)
    (α : Unit →₀ ℕ) :
    VectorPolynomial.coefficients P α ∈
      (F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  exact (F.realification.adapted_iff_coefficients (fun _ : Unit => 1) P).mp hP α

private noncomputable def tensorSubmodulePreimage
    {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (p : Submodule ℚ M) (z : ℝ ⊗[ℚ] M) (hz : z ∈ p.baseChange ℝ) :
    ℝ ⊗[ℚ] p :=
  Classical.choose (Submodule.toBaseChange_surjective' ℝ p hz)

private theorem tensorSubmodulePreimage_spec
    {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (p : Submodule ℚ M) (z : ℝ ⊗[ℚ] M) (hz : z ∈ p.baseChange ℝ) :
    (p.toBaseChange ℝ (tensorSubmodulePreimage p z hz) : ℝ ⊗[ℚ] M) = z :=
  Classical.choose_spec (Submodule.toBaseChange_surjective' ℝ p hz)

private noncomputable def realCoefficientPreimage
    (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P)
    (α : Unit →₀ ℕ) :
    ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α) := by
  change ℝ ⊗[ℚ] (F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toSubmodule
  exact tensorSubmodulePreimage (M := L)
    (F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toSubmodule
    (VectorPolynomial.coefficients P α) (realAdapted_coefficient_mem F P hP α)

private theorem realCoefficientPreimage_spec
    (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P)
    (α : Unit →₀ ℕ) :
    ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ
      (realCoefficientPreimage F P hP α) : ℝ ⊗[ℚ] L) =
        VectorPolynomial.coefficients P α := by
  change (((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toSubmodule).toBaseChange ℝ
    (realCoefficientPreimage F P hP α) : ℝ ⊗[ℚ] L) = VectorPolynomial.coefficients P α
  exact tensorSubmodulePreimage_spec
    (M := L) (F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toSubmodule
    (VectorPolynomial.coefficients P α) (realAdapted_coefficient_mem F P hP α)

private theorem exists_realAdaptedPolynomialMap_preimage
    (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P) :
    ∃ Y : ℝ ⊗[ℚ] Poly F,
      F.realAdaptedPolynomialMap (fun _ : Unit => 1) Y = P := by
  classical
  let f := VectorPolynomial.coefficients P
  let y : ∀ α : Unit →₀ ℕ,
      ℝ ⊗[ℚ] F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α) :=
    fun α => realCoefficientPreimage F P hP α
  have hy' (α : Unit →₀ ℕ) :
      ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ
        (y α) : ℝ ⊗[ℚ] L) = f α := by
    change ((F.layerIdeal (Finsupp.weight (fun _ : Unit => 1) α)).toBaseChange ℝ
      (realCoefficientPreimage F P hP α) : ℝ ⊗[ℚ] L) = VectorPolynomial.coefficients P α
    exact realCoefficientPreimage_spec F P hP α
  let Y : ℝ ⊗[ℚ] Poly F :=
    ∑ α ∈ f.support, (adaptedMonomialLift F α).baseChange ℝ (y α)
  have hPoly : F.realAdaptedPolynomialMap (fun _ : Unit => 1) Y = P := by
    change F.realAdaptedPolynomialMap (fun _ : Unit => 1)
        (∑ α ∈ f.support, (adaptedMonomialLift F α).baseChange ℝ (y α)) = P
    rw [realAdaptedPolynomialMap_monomialSum_coefficients F f y hy']
    exact (VectorPolynomial.coefficients (σ := Unit) (R := ℚ)
      (V := ℝ ⊗[ℚ] L)).symm_apply_apply P
  exact ⟨Y, hPoly⟩

/-- Every adapted real polynomial log has a basepoint in the kernel of the
translation coordinate whose evaluations are the given polynomial values. -/
theorem exists_linearized_basepoint (F : NilpotentLieFiltration L s)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hP : F.realification.Adapted (fun _ : Unit => 1) P) :
    ∃ x : ℝ ⊗[ℚ] Lin F, rLinReal F x = 0 ∧
      ∀ m : ℤ, evLinReal F m x =
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ)) P := by
  classical
  let wt : Unit → ℕ := fun _ => 1
  obtain ⟨Y, hPoly⟩ := exists_realAdaptedPolynomialMap_preimage F P hP
  let inlReal : (ℝ ⊗[ℚ] Poly F) →ₗ[ℝ] (ℝ ⊗[ℚ] Lin F) :=
    (LieAlgebra.SemiDirectSum.inl (shiftAction F)).toLinearMap.baseChange ℝ
  have hr (z : ℝ ⊗[ℚ] Poly F) : rLinReal F (inlReal z) = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul a q =>
        simp [rLinReal, inlReal, rLin, LieAlgebra.SemiDirectSum.projr_inl_apply]
    | add z₁ z₂ hz₁ hz₂ => simp [inlReal, hz₁, hz₂]
  have heval (m : ℤ) (z : ℝ ⊗[ℚ] Poly F) :
      evLinReal F m (inlReal z) =
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
          (F.realAdaptedPolynomialMap wt z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a q =>
        have hleft : evLinReal F m (inlReal (a ⊗ₜ[ℚ] q)) =
            a ⊗ₜ[ℚ] VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
              (q : VectorPolynomial Unit ℚ L) := by
          simp [inlReal, evLinReal, evLin, LieAlgebra.SemiDirectSum.projl_inl_apply]
        exact hleft.trans
          (realAdaptedPolynomialMap_eval_tmul F a q (fun _ : Unit => (m : ℚ))).symm
    | add z₁ z₂ hz₁ hz₂ => simp [inlReal, map_add, hz₁, hz₂]
  refine ⟨inlReal Y, hr Y, ?_⟩
  intro m
  have h := heval m Y
  rw [hPoly] at h
  exact h

private theorem bracket_Dhat_inl {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s) (Q : Poly F) :
    ⁅Dhat F, LieAlgebra.SemiDirectSum.inl (shiftAction F) Q⁆ =
      LieAlgebra.SemiDirectSum.inl (shiftAction F) (shiftAction F 1 Q) := by
  simp [Dhat, LieAlgebra.SemiDirectSum.inr_eq_mk,
    LieAlgebra.SemiDirectSum.inl_eq_mk, LieAlgebra.SemiDirectSum.lie_eq_mk]

theorem evLin_conjugation_shift {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s) (hs : 0 < s)
    (c : ℚ) (m : ℤ) (Q : Poly F) :
    evLin F m (lieBCH (2 * s)
      (lieBCH (2 * s) (c • Dhat F)
        (LieAlgebra.SemiDirectSum.inl (shiftAction F) Q))
      (-(c • Dhat F))) =
      VectorPolynomial.eval (fun _ : Unit => (m : ℚ) + c)
        (Q : VectorPolynomial Unit ℚ L) := by
  let ι : Poly F →ₗ⁅ℚ⁆ Lin F := LieAlgebra.SemiDirectSum.inl (shiftAction F)
  let d : Poly F →ₗ[ℚ] Poly F := shiftAction F 1
  let adc : Module.End ℚ (Lin F) := LieAlgebra.ad ℚ (Lin F) (c • Dhat F)
  have hbracket (R : Poly F) : adc (ι R) = ι (c • d R) := by
    change ⁅c • Dhat F, ι R⁆ = ι (c • d R)
    rw [smul_lie, bracket_Dhat_inl]
    simp [ι, d]
  have hpow (j : ℕ) : (adc ^ j) (ι Q) = c ^ j • ι (d^[j] (Q)) := by
    induction j with
    | zero => simp [adc, ι]
    | succ j ih =>
      conv_lhs => rw [pow_succ']
      simp only [Module.End.mul_apply]
      change ⁅c • Dhat F, (adc ^ j) (ι Q)⁆ =
        c ^ (j + 1) • ι (d^[j + 1] (Q))
      calc
        ⁅c • Dhat F, (adc ^ j) (ι Q)⁆ = adc (c ^ j • ι (d^[j] (Q))) := by
          change adc ((adc ^ j) (ι Q)) = adc (c ^ j • ι (d^[j] (Q)))
          rw [ih]
        _ = c ^ j • adc (ι (d^[j] (Q))) := map_smul adc _ _
        _ = c ^ j • ι (c • d (d^[j] (Q))) := by rw [hbracket]
        _ = c ^ j • (c • ι (d (d^[j] (Q)))) := by
          rw [map_smul]
        _ = (c ^ j * c) • ι (d (d^[j] (Q))) := by rw [smul_smul]
        _ = c ^ (j + 1) • ι (d (d^[j] (Q))) := by
          exact congrArg (fun r : ℚ => r • ι (d (d^[j] (Q)))) (pow_succ c j).symm
        _ = c ^ (j + 1) • ι (d^[j + 1] (Q)) := by
          rw [Function.iterate_succ_apply']
  have hd : shiftAction F 1 = hD F := by
    simpa [shiftAction] using (Classical.choose_spec (exists_shiftAction F) 1)
  have hiter (j : ℕ) :
      (d^[j] (Q) : VectorPolynomial Unit ℚ L) =
        polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      change (shiftAction F 1 (d^[j] (Q)) : VectorPolynomial Unit ℚ L) = _
      rw [hd, hD_apply, ih, Function.iterate_succ_apply']
  have hev (R : Poly F) : evLin F m (ι R) =
      VectorPolynomial.eval (fun _ : Unit => (m : ℚ)) (R : VectorPolynomial Unit ℚ L) := by
    simp [evLin, ι, LieAlgebra.SemiDirectSum.projl_inl_apply]
  have hQadapt : F.Adapted (fun _ : Unit => 1) (Q : VectorPolynomial Unit ℚ L) := by
    apply (F.mem_adaptedSubmodule (fun _ : Unit => 1) _).mp
    change (Q : VectorPolynomial Unit ℚ L) ∈ F.adaptedLieSubalgebra (fun _ : Unit => 1)
    exact Q.property
  have hdegree (j : ℕ) (hj : 2 * s < j) :
      VectorPolynomial.coefficients (Q : VectorPolynomial Unit ℚ L)
          (Finsupp.single () j) = 0 := by
    exact F.adapted_degreeLE (fun _ : Unit => 1) hQadapt (Finsupp.single () j)
      (by simpa [Finsupp.weight_single] using (show s < j by omega))
  have hTaylor := polynomial_translation_taylor (2 * s)
    (Q : VectorPolynomial Unit ℚ L) hdegree c
  have hsum (j : ℕ) :
      evLin F m (((j.factorial : ℚ)⁻¹) • ((adc ^ j) (ι Q))) =
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
          ((c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by
    simp only [map_smul, hpow j, map_smul, hev, hiter j]
    rw [smul_smul]
    congr 1
    ring
  rw [AssemblyAdjoint.lieBCH_conj_eq_exp_ad_aux
    ((weightFiltration F hs).lowerCentralSeries_eq_bot)]
  calc
    evLin F m (∑ j ∈ Finset.range (2 * s + 1),
        ((j.factorial : ℚ)⁻¹) • ((adc ^ j) (ι Q))) =
      ∑ j ∈ Finset.range (2 * s + 1),
        VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
          ((c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact hsum j
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
        (∑ j ∈ Finset.range (2 * s + 1),
          (c ^ j / (j.factorial : ℚ)) •
            polyDeriv^[j] (Q : VectorPolynomial Unit ℚ L)) := by rw [map_sum]
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
        (VectorPolynomial.translate (fun _ : Unit => c) Q) := by rw [hTaylor]
    _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ) + c) Q := by
          rw [VectorPolynomial.eval_translate]

/-- The adjoint polynomial sum itself shifts evaluation by the same amount. -/
theorem evLin_adjoint_sum {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s) (hs : 0 < s)
    (c : ℚ) (m : ℤ) (Q : Poly F) :
    evLin F m (∑ j ∈ Finset.range (2 * s + 1),
      ((j.factorial : ℚ)⁻¹) •
        ((LieAlgebra.ad ℚ (Lin F) (c • Dhat F)) ^ j)
          (LieAlgebra.SemiDirectSum.inl (shiftAction F) Q)) =
      VectorPolynomial.eval (fun _ : Unit => (m : ℚ) + c)
        (Q : VectorPolynomial Unit ℚ L) := by
  have h := evLin_conjugation_shift F hs c m Q
  rw [AssemblyAdjoint.lieBCH_conj_eq_exp_ad_aux
    ((weightFiltration F hs).lowerCentralSeries_eq_bot)] at h
  exact h

end HindmanSumsProducts.InverseBridge
