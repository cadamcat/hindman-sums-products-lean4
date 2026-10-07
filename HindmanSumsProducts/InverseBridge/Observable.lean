import HindmanSumsProducts.InverseBridge.Linear

/-!
The compactly supported interpolation observable and its menu metric (IB.a9--a10).
-/

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3
open Filter
open scoped BigOperators NNReal Topology BoundedContinuousFunction TensorProduct

local instance lineLieRingObservable : LieRing Line := LieRing.ofAssociativeRing
local instance lineLieAlgebraObservable : LieAlgebra ℚ Line := LieAlgebra.ofAssociativeAlgebra
local instance lineIsLieAbelian : IsLieAbelian Line :=
  (isMulCommutative_iff_isLieAbelian (A := Line)).mp inferInstance

local instance realLineIsLieAbelian : IsLieAbelian (ℝ ⊗[ℚ] Line) := by
  refine ⟨?_⟩
  intro x y
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      induction y using TensorProduct.inductionOn with
      | tmul b w =>
          simp [LieAlgebra.ExtendScalars.bracket_tmul, lineIsLieAbelian.trivial]
      | add y₁ y₂ hy₁ hy₂ =>
          calc
            ⁅a ⊗ₜ[ℚ] z, y₁ + y₂⁆ = ⁅a ⊗ₜ[ℚ] z, y₁⁆ + ⁅a ⊗ₜ[ℚ] z, y₂⁆ :=
              LieRing.lie_add _ _ _
            _ = 0 := by rw [hy₁, hy₂]; simp
  | add x₁ x₂ hx₁ hx₂ =>
      calc
        ⁅x₁ + x₂, y⁆ = ⁅x₁, y⁆ + ⁅x₂, y⁆ := LieRing.add_lie _ _ _
        _ = 0 := by rw [hx₁, hx₂]; simp

/-- A triangular bump supported in the interval `(-1/3, 1/3)`. -/
noncomputable def bump (x : ℝ) : ℝ := max 0 (1 - 3 * |x|)

theorem bump_nonneg (x : ℝ) : 0 ≤ bump x := le_max_left _ _

theorem bump_le_one (x : ℝ) : bump x ≤ 1 := by
  unfold bump
  exact max_le (by norm_num) (by nlinarith [abs_nonneg x])

theorem bump_ne_zero_iff (x : ℝ) : bump x ≠ 0 ↔ |x| < 1 / 3 := by
  constructor
  · intro hb
    by_contra h
    have hlarge : 1 / 3 ≤ |x| := le_of_not_gt h
    have hle : 1 - 3 * |x| ≤ 0 := by nlinarith [hlarge]
    have hzero : bump x = 0 := by
      unfold bump
      rw [max_eq_left hle]
    exact hb hzero
  · intro h
    have hpos : 0 < 1 - 3 * |x| := by nlinarith [abs_nonneg x]
    unfold bump
    rw [max_eq_right (le_of_lt hpos)]
    exact ne_of_gt hpos

/-- Only finitely many integer translates can meet the compact support of `bump`. -/
theorem bump_integer_support_finite (r : ℝ) :
    {m : ℤ | bump (r - m) ≠ 0}.Finite := by
  apply (Set.finite_Icc (Int.floor r - 1) (Int.floor r + 2)).subset
  intro m hm
  have habs := (bump_ne_zero_iff (r - m)).mp hm
  have hleft := (abs_lt.mp habs).1
  have hright := (abs_lt.mp habs).2
  have hloR : ((Int.floor r - 1 : ℤ) : ℝ) < (m : ℝ) := by
    have hf := Int.floor_le r
    push_cast
    linarith
  have hhiR : (m : ℝ) < ((Int.floor r + 2 : ℤ) : ℝ) := by
    have hf := Int.lt_floor_add_one r
    push_cast
    linarith
  have hlo : Int.floor r - 1 ≤ m := by exact_mod_cast le_of_lt hloR
  have hlt : m < Int.floor r + 2 := by exact_mod_cast hhiR
  exact Set.mem_Icc.mpr ⟨hlo, le_of_lt hlt⟩

theorem bump_integer_support_subsingleton (r : ℝ) :
    {m : ℤ | bump (r - m) ≠ 0}.Subsingleton := by
  intro m hm n hn
  by_contra hmn
  have hm' : |r - (m : ℝ)| < 1 / 3 := (bump_ne_zero_iff _).mp hm
  have hn' : |r - (n : ℝ)| < 1 / 3 := (bump_ne_zero_iff _).mp hn
  have hsepInt : 1 ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hsep : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by exact_mod_cast hsepInt
  have htriangle : |(m : ℝ) - (n : ℝ)| ≤ |r - (m : ℝ)| + |r - (n : ℝ)| := by
    calc
      |(m : ℝ) - (n : ℝ)| = |(r - (n : ℝ)) - (r - (m : ℝ))| := by congr 1 <;> ring
      _ ≤ |r - (n : ℝ)| + |r - (m : ℝ)| := abs_sub _ _
      _ = |r - (m : ℝ)| + |r - (n : ℝ)| := by ring
  linarith

/-- Interpolate a function on a quotient along the integer translation coordinate. -/
noncomputable def liftObs {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) : ℝ :=
  ∑ᶠ m : ℤ, bump (r x - m) * H (point x m)

/-- The `finsum` defining the interpolation is an ordinary finite sum at each point. -/
theorem liftObs_finite_sum {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) :
    liftObs r point H x =
      ∑ m ∈ (bump_integer_support_finite (r x)).toFinset,
        bump (r x - m) * H (point x m) := by
  let f : ℤ → ℝ := fun m => bump (r x - m) * H (point x m)
  have hfin : {m : ℤ | bump (r x - m) ≠ 0}.Finite := bump_integer_support_finite (r x)
  have hsub : Function.support f ⊆ hfin.toFinset := by
    intro m hm
    have hterm : f m ≠ 0 := hm
    have hbump : bump (r x - m) ≠ 0 := by
      by_contra hb
      exact hterm (by simp [f, hb])
    exact hfin.mem_toFinset.mpr hbump
  rw [liftObs, finsum_eq_sum_of_support_subset f hsub]

/-- The real translation coordinate on the realification of the linearized
semidirect Lie algebra. -/
noncomputable def realTranslationCoordinate {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap.comp (rLinReal F)

private noncomputable def realProjl {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Lin F) →ₗ[ℝ] (ℝ ⊗[ℚ] Poly F) :=
  (LieAlgebra.SemiDirectSum.projl (shiftAction F)).baseChange ℝ

/-- Every realified linearized coordinate is the sum of its polynomial
component and its real translation coordinate. -/
private theorem realInl_realProjl_add_smul {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (x : ℝ ⊗[ℚ] Lin F) :
    realInl F (realProjl F x) + realTranslationCoordinate F x • realDhat F = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      have hcoord : realTranslationCoordinate F (a ⊗ₜ[ℚ] z) =
          z.right • a := by
        simp [realTranslationCoordinate, rLinReal, rLin,
          TensorProduct.AlgebraTensorModule.rid_tmul]
      have htrans : (z.right • a) • realDhat F =
          a ⊗ₜ[ℚ] LieAlgebra.SemiDirectSum.inr (shiftAction F) z.right := by
        calc
          _ = (z.right • a) ⊗ₜ[ℚ] Dhat F := by
                rw [realDhat, TensorProduct.smul_tmul']
                simp
          _ = a ⊗ₜ[ℚ] (z.right • Dhat F) := by
                rw [TensorProduct.smul_tmul]
          _ = _ := by simp [Dhat]
      have hz : z = LieAlgebra.SemiDirectSum.inl (shiftAction F) z.left +
          LieAlgebra.SemiDirectSum.inr (shiftAction F) z.right := by
        apply (LieAlgebra.SemiDirectSum.toProdl (shiftAction F)).injective
        simp [LieAlgebra.SemiDirectSum.toProdl, LieAlgebra.SemiDirectSum.toProd]
      rw [hcoord]
      simp only [realProjl, realInl, LinearMap.baseChange_tmul]
      rw [htrans, hz, TensorProduct.tmul_add]
      simp [LieAlgebra.SemiDirectSum.projl_inl_apply,
        LieAlgebra.SemiDirectSum.projl_inr_apply]
  | add x y hx hy =>
      rw [(realProjl F).map_add, (realInl F).map_add,
        (realTranslationCoordinate F).map_add, add_smul]
      calc
        _ = (realInl F (realProjl F x) + realTranslationCoordinate F x • realDhat F) +
            (realInl F (realProjl F y) + realTranslationCoordinate F y • realDhat F) := by abel
        _ = x + y := by rw [hx, hy]

private theorem realInl_eq_self_of_realTranslation_zero {L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)
    (x : ℝ ⊗[ℚ] Lin F) (hx : realTranslationCoordinate F x = 0) :
    realInl F (realProjl F x) = x := by
  calc
    realInl F (realProjl F x) =
        realInl F (realProjl F x) + realTranslationCoordinate F x • realDhat F := by
          rw [hx]
          simp
    _ = x := realInl_realProjl_add_smul F x

private noncomputable def realifiedInlLieHom {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Poly F) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] Lin F) where
  toLinearMap := (realificationLieHom
    (LieAlgebra.SemiDirectSum.inl (shiftAction F))).toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro x y
    exact (realificationLieHom
      (LieAlgebra.SemiDirectSum.inl (shiftAction F))).map_lie x y

private noncomputable def realEvalLieHom {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (m : ℤ) :
    (ℝ ⊗[ℚ] Poly F) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) :=
  (VectorPolynomial.evalLie (fun _ : Unit => (m : ℚ))).comp
    (F.realAdaptedPolynomialMap (fun _ : Unit => 1))

private theorem evLinReal_lieBCH_of_translation_zero {L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (hs : 0 < s) (m : ℤ)
    (x y : ℝ ⊗[ℚ] Lin F)
    (hx : realTranslationCoordinate F x = 0)
    (hy : realTranslationCoordinate F y = 0) :
    evLinReal F m (lieBCH (2 * s) x y) =
      lieBCH s (evLinReal F m x) (evLinReal F m y) := by
  let X := realProjl F x
  let Y := realProjl F y
  have hx' : realInl F X = x := realInl_eq_self_of_realTranslation_zero F x hx
  have hy' : realInl F Y = y := realInl_eq_self_of_realTranslation_zero F y hy
  have hInl := map_lieBCH (realifiedInlLieHom F) (2 * s) X Y
  change realInl F (lieBCH (2 * s) X Y) =
    lieBCH (2 * s) (realInl F X) (realInl F Y) at hInl
  have hEval (Z : ℝ ⊗[ℚ] Poly F) :
      evLinReal F m (realInl F Z) = realEvalLieHom F m Z := by
    exact evLinReal_realInl_apply F m Z
  calc
    evLinReal F m (lieBCH (2 * s) x y) =
        evLinReal F m (lieBCH (2 * s) (realInl F X) (realInl F Y)) := by
          rw [← hx', ← hy']
    _ = evLinReal F m (realInl F (lieBCH (2 * s) X Y)) := by rw [← hInl]
    _ = realEvalLieHom F m (lieBCH (2 * s) X Y) := hEval _
    _ = lieBCH (2 * s) (realEvalLieHom F m X) (realEvalLieHom F m Y) := by
          rw [map_lieBCH]
    _ = lieBCH s (realEvalLieHom F m X) (realEvalLieHom F m Y) := by
          rw [lieBCH_eq_of_step_le (F.realification.lowerCentralSeries_eq_bot)
            (by omega : s ≤ 2 * s)]
    _ = lieBCH s (evLinReal F m x) (evLinReal F m y) := by
          rw [← hEval X, ← hEval Y, hx', hy']

private theorem rLin_lieBCH {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (hs : 0 < s) (x y : Lin F) :
    rLin F (lieBCH (2 * s) x y) = rLin F x + rLin F y := by
  calc
    rLin F (lieBCH (2 * s) x y) = lieBCH (2 * s) (rLin F x) (rLin F y) := by
      rw [map_lieBCH]
    _ = rLin F x + rLin F y := by
      rw [lieBCH_eq_add_of_isLieAbelian (by omega : 1 ≤ 2 * s)]

private theorem rLin_group_mul {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (g h : (weightFiltration F hs).Group) :
    rLin F (g * h).coord = rLin F g.coord + rLin F h.coord := by
  change rLin F (lieBCH (2 * s) g.coord h.coord) = _
  exact rLin_lieBCH F hs g.coord h.coord

private theorem rLin_group_inv {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (g : (weightFiltration F hs).Group) :
    rLin F (g⁻¹).coord = -rLin F g.coord := by
  change rLin F (-g.coord) = _
  rw [map_neg]

private noncomputable def linearizedShiftElement {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (k : ℤ) : (weightFiltration F hs).realification.Group :=
  ⟨(k : ℝ) • realDhat F⟩

private theorem exists_realification_lattice_factor {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (B : ℕ) (GammaHat : Subgroup (weightFiltration F hs).Group)
    (hcoord : ∀ γ ∈ GammaHat, ∃ z : ℤ, rLin F γ.coord = (B * z : ℚ))
    (hshift : ∀ z : ℤ,
      (⟨(B * z : ℚ) • Dhat F⟩ : (weightFiltration F hs).Group) ∈ GammaHat)
    {γ : (weightFiltration F hs).realification.Group}
    (hγ : γ ∈ GammaHat.map (NilpotentLieBCHGroup.realificationHom
      (hnil := (weightFiltration F hs).lowerCentralSeries_eq_bot))) :
    ∃ k : ℤ, ∃ g₀ : (weightFiltration F hs).Group,
      g₀ ∈ GammaHat ∧ rLin F g₀.coord = 0 ∧
      γ = NilpotentLieBCHGroup.realificationHom g₀ *
        linearizedShiftElement F hs k := by
  classical
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨z, hz⟩ := hcoord g hg
  let k : ℤ := B * z
  let shift : (weightFiltration F hs).Group := ⟨(B * z : ℚ) • Dhat F⟩
  have hshiftmem : shift ∈ GammaHat := by simpa [shift] using hshift z
  let g₀ : (weightFiltration F hs).Group := g * shift⁻¹
  have hg₀ : g₀ ∈ GammaHat := GammaHat.mul_mem hg (GammaHat.inv_mem hshiftmem)
  have hshiftCoord : rLin F shift.coord = (B * z : ℚ) := by
    simp [shift, rLin, Dhat]
  have hg₀coord : rLin F g₀.coord = 0 := by
    rw [rLin_group_mul, rLin_group_inv, hz, hshiftCoord]
    simp [k]
  let γ₀ := NilpotentLieBCHGroup.realificationHom g₀
  have hγ₀mem : γ₀ ∈ GammaHat.map (NilpotentLieBCHGroup.realificationHom
      (hnil := (weightFiltration F hs).lowerCentralSeries_eq_bot)) := by
    exact Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩
  have hγ₀coord : realTranslationCoordinate F γ₀.coord = 0 := by
    simpa [γ₀, realTranslationCoordinate, rLinReal,
      NilpotentLieBCHGroup.realificationHom_coord, hg₀coord]
  let shiftR := linearizedShiftElement F hs k
  have hshiftR : NilpotentLieBCHGroup.realificationHom shift = shiftR := by
    apply NilpotentLieBCHGroup.ext
    change (1 : ℝ) ⊗ₜ[ℚ] ((B * z : ℚ) • Dhat F) =
      (k : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] Dhat F)
    calc
      _ = (B * z : ℚ) • ((1 : ℝ) ⊗ₜ[ℚ] Dhat F) :=
        TensorProduct.tmul_smul (R := ℚ) (B * z : ℚ) (1 : ℝ) (Dhat F)
      _ = ((B * z : ℚ) : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] Dhat F) := by
        symm
        simpa using (IsScalarTower.algebraMap_smul (R := ℚ) (A := ℝ)
          (B * z : ℚ) ((1 : ℝ) ⊗ₜ[ℚ] Dhat F))
      _ = (k : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] Dhat F) := by simp [k]
  refine ⟨k, g₀, hg₀, hg₀coord, ?_⟩
  have hfactor : γ₀ * shiftR = NilpotentLieBCHGroup.realificationHom g := by
    change NilpotentLieBCHGroup.realificationHom (g * shift⁻¹) * shiftR =
      NilpotentLieBCHGroup.realificationHom g
    rw [← hshiftR, map_mul, map_inv]
    simp
  simpa [γ₀, shiftR] using hfactor.symm

/-- Remove the translation coordinate by an integer evaluation shift, then
evaluate the polynomial component in the original quotient. -/
noncomputable def linearizedObservablePoint {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 0 < s) (m : ℤ)
    (X : (weightFiltration D.filtration hs).realification.Group) : D.Space := by
  let r := realTranslationCoordinate D.filtration X.coord
  exact QuotientGroup.mk
    (⟨evLinReal D.filtration m
      ((⟨-r • realDhat D.filtration⟩ * X).coord)⟩ : D.filtration.realification.Group)

/-- The compactly supported interpolation lift on the linearized group. -/
noncomputable def linearizedObservableLift {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (H : D.Space → ℝ) :
    (weightFiltration D.filtration hs).realification.Group → ℝ :=
  liftObs (fun X => realTranslationCoordinate D.filtration X.coord)
    (fun X m => linearizedObservablePoint D hs m X) H

private noncomputable def realRationalLieHom {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) :
    (ℝ ⊗[ℚ] Lin F) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] Line) where
  toLinearMap := (realificationLieHom (rLin F)).toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro x y
    exact (realificationLieHom (rLin F)).map_lie x y

private theorem realTranslationCoordinate_lieBCH {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (x y : ℝ ⊗[ℚ] Lin F) :
    realTranslationCoordinate F (lieBCH (2 * s) x y) =
      realTranslationCoordinate F x + realTranslationCoordinate F y := by
  let f := realRationalLieHom F
  have hcoord (z : ℝ ⊗[ℚ] Lin F) :
      realTranslationCoordinate F z =
        TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ (f z) := by
    change TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ (rLinReal F z) =
      TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ (f z)
    have hf : f z = rLinReal F z := rfl
    rw [hf]
  calc
    realTranslationCoordinate F (lieBCH (2 * s) x y) =
        TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ (f (lieBCH (2 * s) x y)) := hcoord _
    _ = TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ
          (lieBCH (2 * s) (f x) (f y)) := by rw [map_lieBCH]
    _ = TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ (f x + f y) := by
          rw [lieBCH_eq_add_of_isLieAbelian (by omega : 1 ≤ 2 * s)]
    _ = realTranslationCoordinate F x + realTranslationCoordinate F y := by
          rw [(TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).map_add, ← hcoord, ← hcoord]

private noncomputable def realTranslationElement {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (c : ℝ) : (weightFiltration F hs).realification.Group :=
  ⟨c • realDhat F⟩

private theorem realTranslationElement_coord {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (c : ℝ) :
    realTranslationCoordinate F (realTranslationElement F hs c).coord = c := by
  simp [realTranslationElement, realTranslationCoordinate, rLinReal, realDhat,
    rLin, Dhat, TensorProduct.AlgebraTensorModule.rid_tmul]

private theorem realTranslationElement_mul {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (c d : ℝ) :
    realTranslationElement F hs c * realTranslationElement F hs d =
      realTranslationElement F hs (c + d) := by
  apply NilpotentLieBCHGroup.ext
  change lieBCH (2 * s) (c • realDhat F) (d • realDhat F) = (c + d) • realDhat F
  rw [lieBCH_eq_add_of_lie_eq_zero
    (weightFiltration F hs).realification.lowerCentralSeries_eq_bot]
  · rw [add_smul]
  · simp

private theorem realTranslationCoordinate_group_mul {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (g h : (weightFiltration F hs).realification.Group) :
    realTranslationCoordinate F (g * h).coord =
      realTranslationCoordinate F g.coord + realTranslationCoordinate F h.coord := by
  change realTranslationCoordinate F (lieBCH (2 * s) g.coord h.coord) = _
  exact realTranslationCoordinate_lieBCH F hs g.coord h.coord

private theorem linearizedObservablePoint_factor {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s) (m : ℤ)
    (X : (weightFiltration D.filtration hs).realification.Group)
    (g₀ : (weightFiltration D.filtration hs).Group)
    (hg₀r : rLin D.filtration g₀.coord = 0) (k : ℤ)
    (hEval : ∀ n : ℤ,
      (⟨evLin D.filtration n g₀.coord⟩ : D.filtration.Group) ∈ D.lattice) :
    linearizedObservablePoint D hs (m + k)
        (X * NilpotentLieBCHGroup.realificationHom g₀ *
          linearizedShiftElement D.filtration hs k) =
      linearizedObservablePoint D hs m X := by
  let F := D.filtration
  let γ₀ := NilpotentLieBCHGroup.realificationHom g₀
  let shift := linearizedShiftElement F hs k
  let r := realTranslationCoordinate F X.coord
  let rY := realTranslationCoordinate F (X * γ₀ * shift).coord
  let innerX := realTranslationElement F hs (-r) * X
  let innerY := innerX * γ₀
  let innerNew := realTranslationElement F hs (-rY) * (X * γ₀ * shift)
  have hγ₀r : realTranslationCoordinate F γ₀.coord = 0 := by
    simpa [γ₀, realTranslationCoordinate, rLinReal,
      NilpotentLieBCHGroup.realificationHom_coord] using congrArg (fun q : ℚ => (q : ℝ)) hg₀r
  have hshiftCoord : realTranslationCoordinate F shift.coord = k := by
    change realTranslationCoordinate F (realTranslationElement F hs k).coord = k
    exact realTranslationElement_coord F hs k
  have hrY : rY = r + k := by
    change realTranslationCoordinate F
      (lieBCH (2 * s) (lieBCH (2 * s) X.coord γ₀.coord) shift.coord) =
      realTranslationCoordinate F X.coord + k
    rw [realTranslationCoordinate_lieBCH F hs
      (lieBCH (2 * s) X.coord γ₀.coord) shift.coord,
      realTranslationCoordinate_lieBCH F hs X.coord γ₀.coord,
      hγ₀r, hshiftCoord]
    ring
  have hinnerX : realTranslationCoordinate F innerX.coord = 0 := by
    change realTranslationCoordinate F
      (lieBCH (2 * s) (realTranslationElement F hs (-r)).coord X.coord) = 0
    rw [realTranslationCoordinate_lieBCH F hs,
      realTranslationElement_coord F hs (-r)]
    ring
  have hinnerY : realTranslationCoordinate F innerY.coord = 0 := by
    change realTranslationCoordinate F
      (lieBCH (2 * s) innerX.coord γ₀.coord) = 0
    rw [realTranslationCoordinate_lieBCH F hs, hinnerX, hγ₀r]
    simp
  have hTsum : realTranslationElement F hs (-(r + k)) =
      realTranslationElement F hs (-k) * realTranslationElement F hs (-r) := by
    calc
      realTranslationElement F hs (-(r + k)) =
          realTranslationElement F hs (-k + -r) := by congr 1 <;> ring
      _ = realTranslationElement F hs (-k) * realTranslationElement F hs (-r) :=
          (realTranslationElement_mul F hs (-k) (-r)).symm
  have hinnerFactor : innerNew =
      realTranslationElement F hs (-k) * innerY * realTranslationElement F hs k := by
    dsimp [innerNew, innerY, innerX]
    rw [hrY, hTsum]
    rw [show shift = realTranslationElement F hs k by rfl]
    group
  let poly := realProjl F innerY.coord
  have hpoly : realInl F poly = innerY.coord :=
    realInl_eq_self_of_realTranslation_zero F innerY.coord hinnerY
  have hpolyGroup : (⟨realInl F poly⟩ : (weightFiltration F hs).realification.Group) =
      innerY := by
    apply NilpotentLieBCHGroup.ext
    exact hpoly
  have hConjEval :
      evLinReal F (m + k)
          (realTranslationElement F hs (-k) * innerY *
            realTranslationElement F hs k).coord =
        evLinReal F m innerY.coord := by
    calc
      _ = VectorPolynomial.eval (fun _ : Unit => ((m + k : ℤ) : ℚ) + (-k : ℚ))
            (F.realAdaptedPolynomialMap (fun _ : Unit => 1) poly) := by
              rw [← hpolyGroup]
              change evLinReal F (m + k) (lieBCH (2 * s)
                (lieBCH (2 * s) ((-(k : ℝ)) • realDhat F) (realInl F poly))
                ((k : ℝ) • realDhat F)) = _
              simpa [Int.cast_neg, neg_smul] using
                (evLinReal_conjugation_shift F hs (-k : ℚ) (m + k) poly)
      _ = VectorPolynomial.eval (fun _ : Unit => (m : ℚ))
            (F.realAdaptedPolynomialMap (fun _ : Unit => 1) poly) := by
              rw [show (fun _ : Unit => ((m + k : ℤ) : ℚ) + (-k : ℚ)) =
                (fun _ : Unit => (m : ℚ)) by
                  funext _
                  push_cast
                  ring]
      _ = evLinReal F m innerY.coord := by
              rw [← hpoly]
              exact (evLinReal_realInl_apply F m poly).symm
  have hγ₀Eval :
      (⟨evLinReal F m γ₀.coord⟩ : F.realification.Group) ∈ D.realLattice := by
    have hcoord : (⟨evLinReal F m γ₀.coord⟩ : F.realification.Group) =
        NilpotentLieBCHGroup.realificationHom
          (⟨evLin F m g₀.coord⟩ : F.Group) := by
      apply NilpotentLieBCHGroup.ext
      rw [NilpotentLieBCHGroup.realificationHom_coord]
      change (evLin F m).baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] g₀.coord) =
        (1 : ℝ) ⊗ₜ[ℚ] evLin F m g₀.coord
      rw [LinearMap.baseChange_tmul]
    rw [hcoord]
    exact Subgroup.mem_map.mpr ⟨⟨evLin F m g₀.coord⟩, hEval m, rfl⟩
  have hinnerEval : evLinReal F m innerY.coord =
      lieBCH s (evLinReal F m innerX.coord) (evLinReal F m γ₀.coord) := by
    change evLinReal F m (lieBCH (2 * s) innerX.coord γ₀.coord) = _
    exact evLinReal_lieBCH_of_translation_zero F hs m
      innerX.coord γ₀.coord hinnerX hγ₀r
  let a : F.realification.Group := ⟨evLinReal F m innerX.coord⟩
  let b : F.realification.Group := ⟨evLinReal F m γ₀.coord⟩
  have hnewEval : evLinReal F (m + k) innerNew.coord = lieBCH s a.coord b.coord := by
    calc
      evLinReal F (m + k) innerNew.coord =
          evLinReal F (m + k)
            (realTranslationElement F hs (-k) * innerY *
              realTranslationElement F hs k).coord := by rw [hinnerFactor]
      _ = evLinReal F m innerY.coord := hConjEval
      _ = lieBCH s a.coord b.coord := by
          simpa [a, b] using hinnerEval
  have hquot : (QuotientGroup.mk (a * b) : D.Space) = QuotientGroup.mk a := by
    apply QuotientGroup.eq.2
    change (a * b)⁻¹ * a ∈ D.realLattice
    simpa [mul_inv_rev] using D.realLattice.inv_mem hγ₀Eval
  change QuotientGroup.mk (⟨evLinReal F (m + k) innerNew.coord⟩ : F.realification.Group) = _
  rw [hnewEval]
  change QuotientGroup.mk (a * b) = QuotientGroup.mk a
  exact hquot

private theorem linearizedObservableLift_invariant {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (B : ℕ) (GammaHat : Subgroup (weightFiltration D.filtration hs).Group)
    (hcoord : ∀ γ ∈ GammaHat,
      ∃ z : ℤ, rLin D.filtration γ.coord = (B * z : ℚ))
    (hshift : ∀ z : ℤ,
      (⟨(B * z : ℚ) • Dhat D.filtration⟩ :
        (weightFiltration D.filtration hs).Group) ∈ GammaHat)
    (hEval : ∀ (g : (weightFiltration D.filtration hs).Group), g ∈ GammaHat →
      rLin D.filtration g.coord = 0 → ∀ n : ℤ,
        (⟨evLin D.filtration n g.coord⟩ : D.filtration.Group) ∈ D.lattice)
    (H : D.Space → ℝ) (X : (weightFiltration D.filtration hs).realification.Group)
    {γ : (weightFiltration D.filtration hs).realification.Group}
    (hγ : γ ∈ GammaHat.map (NilpotentLieBCHGroup.realificationHom
      (hnil := (weightFiltration D.filtration hs).lowerCentralSeries_eq_bot))) :
    linearizedObservableLift D hs H (X * γ) = linearizedObservableLift D hs H X := by
  classical
  let F := D.filtration
  obtain ⟨k, g₀, hg₀, hg₀r, hfactor⟩ :=
    exists_realification_lattice_factor F hs B GammaHat hcoord hshift hγ
  have hEval₀ : ∀ n : ℤ,
      (⟨evLin F n g₀.coord⟩ : F.Group) ∈ D.lattice := hEval g₀ hg₀ hg₀r
  have hpoint (n : ℤ) :
      linearizedObservablePoint D hs (n + k) (X * γ) =
        linearizedObservablePoint D hs n X := by
    rw [hfactor]
    rw [← mul_assoc]
    exact linearizedObservablePoint_factor D hs n X g₀ hg₀r k hEval₀
  let r : ℝ := realTranslationCoordinate F X.coord
  let r' : ℝ := realTranslationCoordinate F (X * γ).coord
  let γ₀ := NilpotentLieBCHGroup.realificationHom g₀
  let shift := linearizedShiftElement F hs k
  have hrγ₀ : realTranslationCoordinate F γ₀.coord = 0 := by
    simpa [γ₀, realTranslationCoordinate, rLinReal,
      NilpotentLieBCHGroup.realificationHom_coord] using congrArg (fun q : ℚ => (q : ℝ)) hg₀r
  have hshiftCoord : realTranslationCoordinate F shift.coord = k := by
    change realTranslationCoordinate F (realTranslationElement F hs k).coord = k
    exact realTranslationElement_coord F hs k
  have hr' : r' = r + k := by
    change realTranslationCoordinate F (X * γ).coord =
      realTranslationCoordinate F X.coord + k
    calc
      realTranslationCoordinate F (X * γ).coord =
          realTranslationCoordinate F (X * (γ₀ * shift)).coord := by rw [hfactor]
      _ = realTranslationCoordinate F ((X * γ₀) * shift).coord := by rw [← mul_assoc]
      _ = realTranslationCoordinate F X.coord + k := by
          rw [realTranslationCoordinate_group_mul F hs (X * γ₀) shift,
            realTranslationCoordinate_group_mul F hs X γ₀, hrγ₀, hshiftCoord]
          ring
  unfold linearizedObservableLift
  rw [liftObs_finite_sum, liftObs_finite_sum]
  apply Finset.sum_bij (fun n _ => n - k)
  · intro n hn
    have hn' := (bump_integer_support_finite r').mem_toFinset.mp hn
    have heq : bump (r' - (n : ℝ)) = bump (r - ((n - k : ℤ) : ℝ)) := by
      rw [hr']
      congr 1
      push_cast
      ring
    apply (bump_integer_support_finite r).mem_toFinset.mpr
    change bump (r - ((n - k : ℤ) : ℝ)) ≠ 0
    rw [← heq]
    exact hn'
  · intro n hn n' hn' hnn'
    omega
  · intro n hn
    have hn' := (bump_integer_support_finite r).mem_toFinset.mp hn
    refine ⟨n + k, ?_, by omega⟩
    have heq : bump (r' - ((n + k : ℤ) : ℝ)) = bump (r - (n : ℝ)) := by
      rw [hr']
      congr 1
      push_cast
      ring
    apply (bump_integer_support_finite r').mem_toFinset.mpr
    change bump (r' - ((n + k : ℤ) : ℝ)) ≠ 0
    rw [heq]
    exact hn'
  · intro n hn
    have heq : bump (r' - (n : ℝ)) = bump (r - ((n - k : ℤ) : ℝ)) := by
      rw [hr']
      congr 1
      push_cast
      ring
    have hp := hpoint (n - k)
    have hidx : n - k + k = n := by omega
    rw [hidx] at hp
    rw [heq, hp]

/-- Bounded observables remain bounded under the triangular interpolation. -/
theorem liftObs_abs_le_one {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (hH : ∀ y, |H y| ≤ 1) (x : X) :
    |liftObs r point H x| ≤ 1 := by
  rw [liftObs_finite_sum]
  have hfinite := bump_integer_support_finite (r x)
  have hcard : (hfinite.toFinset).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro m hm n hn
    exact bump_integer_support_subsingleton (r x)
      (hfinite.mem_toFinset.mp hm) (hfinite.mem_toFinset.mp hn)
  have hterm (m : ℤ) :
      |bump (r x - m) * H (point x m)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (bump_nonneg _)]
    calc
      bump (r x - m) * |H (point x m)| ≤ bump (r x - m) * 1 :=
        mul_le_mul_of_nonneg_left (hH _) (bump_nonneg _)
      _ ≤ 1 := by simpa using bump_le_one (r x - m)
  by_cases hEmpty : hfinite.toFinset = ∅
  · simp [hEmpty]
  · have hnonempty : (hfinite.toFinset).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hcardOne : (hfinite.toFinset).card = 1 := by
      have hpos := Finset.card_pos.mpr hnonempty
      omega
    obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hcardOne
    rw [hm]
    simpa using hterm m

theorem liftObs_scale {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (c : ℝ) (x : X) :
    liftObs r point (fun y => c * H y) x = c * liftObs r point H x := by
  rw [liftObs_finite_sum, liftObs_finite_sum]
  calc
    _ = ∑ m ∈ (bump_integer_support_finite (r x)).toFinset,
          c * (bump (r x - m) * H (point x m)) := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
    _ = c * ∑ m ∈ (bump_integer_support_finite (r x)).toFinset,
          bump (r x - m) * H (point x m) := by rw [Finset.mul_sum]

theorem liftObs_mem_Icc {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (hH : ∀ y, H y ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    liftObs r point H x ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ liftObs r point H x := by
    rw [liftObs_finite_sum]
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (bump_nonneg _) (hH _).1
  have hHabs : ∀ y, |H y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (hH y).1]
    exact (hH y).2
  have habs := liftObs_abs_le_one r point H hHabs x
  exact ⟨hnonneg, (abs_le.mp habs).2⟩

/-- At an integral translation coordinate only the matching translate contributes. -/
theorem liftObs_at_integer {X Y : Type*} (r : X → ℝ) (point : X → ℤ → Y)
    (H : Y → ℝ) (x : X) (n : ℤ) (hr : r x = n)
    (hzero : ∀ m : ℤ, m ≠ n → bump (r x - m) = 0) :
    liftObs r point H x = H (point x n) := by
  rw [liftObs, finsum_eq_single
    (fun m : ℤ => bump (r x - m) * H (point x m)) n]
  · simp [hr, bump]
  · intro m hm
    simp [hzero m hm]

/-- An observable lift together with the lattice invariance needed to descend it. -/
structure ObservableDescent (G : Type*) [Group G] (Γ : Subgroup G) (Y : Type*) where
  lift : (Y → ℝ) → G → ℝ
  desc : (Y → ℝ) → G ⧸ Γ → ℝ
  desc_mk : ∀ H g, desc H (QuotientGroup.mk g) = lift H g
  invariant : ∀ H g γ, γ ∈ Γ → lift H (g * γ) = lift H g
  scale : ∀ (c : ℝ) H x, desc (fun y => c * H y) x = c * desc H x
  unit_bound : ∀ H, (∀ y, |H y| ≤ 1) → ∀ x, |desc H x| ≤ 1

namespace ObservableDescent

/-- Descend an invariant lift on left-coset quotients, preserving scaling and bounds. -/
noncomputable def ofLift {G : Type*} [Group G] (Γ : Subgroup G) {Y : Type*}
    (lift : (Y → ℝ) → G → ℝ)
    (hinv : ∀ H g γ, γ ∈ Γ → lift H (g * γ) = lift H g)
    (hscale : ∀ c H g, lift (fun y => c * H y) g = c * lift H g)
    (hbound : ∀ H, (∀ y, |H y| ≤ 1) → ∀ g, |lift H g| ≤ 1) :
    ObservableDescent G Γ Y where
  lift := lift
  desc H := Quotient.lift (lift H) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ Γ := (QuotientGroup.leftRel_apply).mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb]
    exact (hinv H a _ hab').symm)
  desc_mk := by
    intro H g
    rfl
  invariant := hinv
  scale := by
    intro c H x
    refine Quotient.inductionOn x ?_
    intro g
    simp only [Quotient.lift_mk]
    exact hscale c H g
  unit_bound := by
    intro H hH x
    refine Quotient.inductionOn x ?_
    intro g
    simp only [Quotient.lift_mk]
    exact hbound H hH g

end ObservableDescent

/-- The normalized, one-Lipschitz observables used to define the custom metric. -/
def LipOne (Y : Type*) [MetricSpace Y] :=
  {H : Y → ℝ // (∀ y, |H y| ≤ 1) ∧ LipschitzWith 1 H}

/-- The concrete interpolation descends to the linearized quotient for any
integral lattice satisfying the a5 coordinate and evaluation conditions. -/
private noncomputable def linearizedObservableDescent {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s) (B : ℕ)
    (GammaHat : Subgroup (weightFiltration D.filtration hs).Group)
    (hcoord : ∀ γ ∈ GammaHat,
      ∃ z : ℤ, rLin D.filtration γ.coord = (B * z : ℚ))
    (hshift : ∀ z : ℤ,
      (⟨(B * z : ℚ) • Dhat D.filtration⟩ :
        (weightFiltration D.filtration hs).Group) ∈ GammaHat)
    (hEval : ∀ (g : (weightFiltration D.filtration hs).Group), g ∈ GammaHat →
      rLin D.filtration g.coord = 0 → ∀ n : ℤ,
        (⟨evLin D.filtration n g.coord⟩ : D.filtration.Group) ∈ D.lattice) :
    ObservableDescent
      (weightFiltration D.filtration hs).realification.Group
      (GammaHat.map (NilpotentLieBCHGroup.realificationHom
        (hnil := (weightFiltration D.filtration hs).lowerCentralSeries_eq_bot))) D.Space := by
  let ΓR := GammaHat.map (NilpotentLieBCHGroup.realificationHom
    (hnil := (weightFiltration D.filtration hs).lowerCentralSeries_eq_bot))
  apply ObservableDescent.ofLift ΓR (linearizedObservableLift D hs)
  · intro H g γ hγ
    exact linearizedObservableLift_invariant D hs B GammaHat hcoord hshift hEval H g hγ
  · intro c H g
    simpa [linearizedObservableLift] using
      (liftObs_scale (fun X => realTranslationCoordinate D.filtration X.coord)
        (fun X n => linearizedObservablePoint D hs n X) H c g)
  · intro H hH g
    simpa [linearizedObservableLift] using
      (liftObs_abs_le_one (fun X => realTranslationCoordinate D.filtration X.coord)
        (fun X n => linearizedObservablePoint D hs n X) H hH g)

set_option maxHeartbeats 10000000 in
private theorem linearizedObservableLift_range {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (H : D.Space → ℝ) (hH : ∀ y, H y ∈ Set.Icc (0 : ℝ) 1)
    (X : (weightFiltration D.filtration hs).realification.Group) :
    linearizedObservableLift D hs H X ∈ Set.Icc (0 : ℝ) 1 := by
  simpa only [linearizedObservableLift] using
    (liftObs_mem_Icc (fun X => realTranslationCoordinate D.filtration X.coord)
      (fun X n => linearizedObservablePoint D hs n X) H hH X)

private theorem bumpSupport_in_floorInterval {r₀ r : ℝ} (hr : |r - r₀| < 1)
    {m : ℤ} (hm : bump (r - m) ≠ 0) :
    m ∈ Finset.Icc (Int.floor r₀ - 3) (Int.floor r₀ + 3) := by
  have hb := (bump_ne_zero_iff (r - m)).mp hm
  have hL : -(1 / 3 : ℝ) < r - m := (abs_lt.mp hb).1
  have hU : r - m < 1 / 3 := (abs_lt.mp hb).2
  have hrL : -1 < r - r₀ := (abs_lt.mp hr).1
  have hrU : r - r₀ < 1 := (abs_lt.mp hr).2
  have hfL := Int.floor_le r₀
  have hfU := Int.lt_floor_add_one r₀
  have hmL : ((Int.floor r₀ - 3 : ℤ) : ℝ) ≤ (m : ℝ) := by
    push_cast
    linarith
  have hmU : (m : ℝ) ≤ ((Int.floor r₀ + 3 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hmL, by exact_mod_cast hmU⟩

private theorem liftObs_sum_on_interval {X Y : Type*} (r : X → ℝ)
    (point : X → ℤ → Y) (H : Y → ℝ) (I : Finset ℤ) (x : X)
    (hI : {m : ℤ | bump (r x - m) ≠ 0} ⊆ I) :
    liftObs r point H x =
      ∑ m ∈ I, bump (r x - m) * H (point x m) := by
  rw [liftObs_finite_sum]
  apply Finset.sum_subset
  · intro m hm
    exact hI ((bump_integer_support_finite (r x)).mem_toFinset.mp hm)
  · intro m hm hmI
    have hzero : bump (r x - m) = 0 := by
      by_contra hne
      exact hmI ((bump_integer_support_finite (r x)).mem_toFinset.mpr hne)
    simp [hzero]

private theorem bump_lipschitz : LipschitzWith 3 bump := by
  have hlin : LipschitzWith 3 (fun x : ℝ => 1 - 3 * |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change abs ((1 - 3 * abs x) - (1 - 3 * abs y)) ≤ (3 : ℝ) * dist x y
    rw [dist_eq_norm, Real.norm_eq_abs]
    calc
      abs ((1 - 3 * abs x) - (1 - 3 * abs y)) = 3 * abs (abs x - abs y) := by
        rw [show (1 - 3 * |x|) - (1 - 3 * |y|) = -3 * (|x| - |y|) by ring]
        rw [abs_mul]
        norm_num
      _ ≤ 3 * abs (x - y) := by
        exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by norm_num)
  change LipschitzWith 3 (fun x : ℝ => max 0 (1 - 3 * abs x))
  exact hlin.const_max 0

private theorem continuous_linearizedObservablePoint {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] Lin D.filtration)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] Lin D.filtration)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] Lin D.filtration)]
    [T2Space (ℝ ⊗[ℚ] Lin D.filtration)]
    [FiniteDimensional ℝ (ℝ ⊗[ℚ] Lin D.filtration)]
    [IsTopologicalGroup (weightFiltration D.filtration hs).realification.Group]
    (m : ℤ) :
    Continuous (linearizedObservablePoint D hs m) := by
  let F := D.filtration
  have hcoord : Continuous (fun X : (weightFiltration F hs).realification.Group => X.coord) :=
    NilpotentLieBCHGroup.continuous_coord
  have hr : Continuous (fun X : (weightFiltration F hs).realification.Group =>
      realTranslationCoordinate F X.coord) :=
    (LinearMap.continuous_of_finiteDimensional (realTranslationCoordinate F)).comp hcoord
  have hscalar : Continuous (fun X : (weightFiltration F hs).realification.Group =>
      -realTranslationCoordinate F X.coord) := continuous_neg.comp hr
  have hvector : Continuous (fun _ : (weightFiltration F hs).realification.Group =>
      realDhat F) := continuous_const
  have hshift : Continuous (fun X : (weightFiltration F hs).realification.Group =>
      (⟨-realTranslationCoordinate F X.coord • realDhat F⟩ :
        (weightFiltration F hs).realification.Group)) := by
    exact NilpotentLieBCHGroup.continuous_mk.comp
      (hscalar.smul hvector)
  have hmul : Continuous (fun X =>
      (⟨-realTranslationCoordinate F X.coord • realDhat F⟩ :
        (weightFiltration F hs).realification.Group) * X) :=
    hshift.mul continuous_id
  have hcoord' : Continuous (fun X =>
      ((⟨-realTranslationCoordinate F X.coord • realDhat F⟩ :
        (weightFiltration F hs).realification.Group) * X).coord) :=
    hcoord.comp hmul
  have hev : Continuous (fun X => evLinReal F m
      ((⟨-realTranslationCoordinate F X.coord • realDhat F⟩ :
        (weightFiltration F hs).realification.Group) * X).coord) :=
    (LinearMap.continuous_of_finiteDimensional (evLinReal F m)).comp hcoord'
  exact QuotientGroup.continuous_mk.comp
    (NilpotentLieBCHGroup.continuous_mk.comp hev)

private theorem linearizedObservableLift_locally_equi {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] Lin D.filtration)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] Lin D.filtration)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] Lin D.filtration)]
    [T2Space (ℝ ⊗[ℚ] Lin D.filtration)]
    [FiniteDimensional ℝ (ℝ ⊗[ℚ] Lin D.filtration)]
    [IsTopologicalGroup (weightFiltration D.filtration hs).realification.Group]
    (X₀ : (weightFiltration D.filtration hs).realification.Group)
    (ε : ℝ) (hε : 0 < ε) :
    letI : MetricSpace D.Space := D.metricSpace;
    ∃ U ∈ 𝓝 X₀, ∀ X ∈ U, ∀ H : LipOne D.Space,
      |linearizedObservableLift D hs H.1 X - linearizedObservableLift D hs H.1 X₀| < ε := by
  classical
  letI : MetricSpace D.Space := D.metricSpace
  let F := D.filtration
  let r : (weightFiltration F hs).realification.Group → ℝ :=
    fun X => realTranslationCoordinate F X.coord
  let point := fun X m => linearizedObservablePoint D hs m X
  let I : Finset ℤ := Finset.Icc (Int.floor (r X₀) - 3) (Int.floor (r X₀) + 3)
  let τ : ℝ := ε / (4 * ((I.card : ℝ) + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hrcont : Continuous r := by
    exact (LinearMap.continuous_of_finiteDimensional (realTranslationCoordinate F)).comp
      NilpotentLieBCHGroup.continuous_coord
  have hnearR : ∀ᶠ X in 𝓝 X₀, |r X - r X₀| < 1 := by
    have hball : Metric.ball (r X₀) 1 ∈ 𝓝 (r X₀) := Metric.ball_mem_nhds _ (by norm_num)
    have hpre := hrcont.continuousAt.preimage_mem_nhds hball
    filter_upwards [hpre] with X hX
    have hdist : dist (r X) (r X₀) < 1 := by
      simpa [Metric.mem_ball] using hX
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hdist
  have htermNear (m : ℤ) : ∀ᶠ X in 𝓝 X₀,
      |bump (r X - m) - bump (r X₀ - m)| < τ ∧
        dist (point X m) (point X₀ m) < τ := by
    have hbcont : Continuous (fun X : (weightFiltration F hs).realification.Group =>
        bump (r X - m)) := by fun_prop [bump]
    have hbball : Metric.ball (bump (r X₀ - m)) τ ∈ 𝓝 (bump (r X₀ - m)) :=
      Metric.ball_mem_nhds _ hτ
    have hbevent := hbcont.continuousAt.preimage_mem_nhds hbball
    have hpcont := continuous_linearizedObservablePoint D hs m
    have htop : D.metricSpace.toUniformSpace.toTopologicalSpace =
        QuotientGroup.instTopologicalSpace D.realLattice := by
      exact realificationQuotientMetricSpace_topology D.basis D.lattice D.grid
        D.grid_pos D.outer_grid
    have hpball : Metric.ball (point X₀ m) τ ∈ 𝓝 (point X₀ m) := by
      have hpballMetric : Metric.ball (point X₀ m) τ ∈
          @nhds D.Space D.metricSpace.toUniformSpace.toTopologicalSpace (point X₀ m) :=
        Metric.ball_mem_nhds _ hτ
      rw [htop] at hpballMetric
      exact hpballMetric
    have hpevent := hpcont.continuousAt.preimage_mem_nhds hpball
    filter_upwards [hbevent, hpevent] with X hb hp
    constructor
    · have hd : dist (bump (r X - m)) (bump (r X₀ - m)) < τ := by
        simpa [Metric.mem_ball] using hb
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hd
    · simpa [Metric.mem_ball] using hp
  have htermAll : ∀ᶠ X in 𝓝 X₀, ∀ m ∈ I,
      |bump (r X - m) - bump (r X₀ - m)| < τ ∧
        dist (point X m) (point X₀ m) < τ := by
    classical
    induction I using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (by simp)
    | @insert m I hm ih =>
        filter_upwards [htermNear m, ih] with X hX hI
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hX
        · exact hI j hj
  let U : Set (weightFiltration F hs).realification.Group := fun X =>
    (abs (r X - r X₀) < 1) ∧
      ∀ m ∈ I, |bump (r X - m) - bump (r X₀ - m)| < τ ∧
        dist (point X m) (point X₀ m) < τ
  have hU : U ∈ 𝓝 X₀ := by
    filter_upwards [hnearR, htermAll] with X hR hterms
    exact ⟨hR, hterms⟩
  refine ⟨U, hU, ?_⟩
  intro X hX H
  have hsupport (Y : (weightFiltration F hs).realification.Group)
      (hY : |r Y - r X₀| < 1) :
      {m : ℤ | bump (r Y - m) ≠ 0} ⊆ (I : Set ℤ) := by
    intro m hm
    change m ∈ I
    exact bumpSupport_in_floorInterval hY hm
  have hsumY : linearizedObservableLift D hs H.1 X =
      ∑ m ∈ I, bump (r X - m) * H.1 (point X m) := by
    unfold linearizedObservableLift
    exact liftObs_sum_on_interval r point H.1 I X (hsupport X hX.1)
  have hsum0 : linearizedObservableLift D hs H.1 X₀ =
      ∑ m ∈ I, bump (r X₀ - m) * H.1 (point X₀ m) := by
    unfold linearizedObservableLift
    exact liftObs_sum_on_interval r point H.1 I X₀ (hsupport X₀ (by simp))
  have hterm (m : ℤ) (hm : m ∈ I) :
      |bump (r X - m) * H.1 (point X m) -
        bump (r X₀ - m) * H.1 (point X₀ m)| ≤ 2 * τ := by
    have hn := hX.2 m hm
    have hHlip : |H.1 (point X m) - H.1 (point X₀ m)| ≤
        dist (point X m) (point X₀ m) := by
      have h := H.2.2.dist_le_mul (point X m) (point X₀ m)
      simpa [dist_eq_norm, Real.norm_eq_abs] using h
    have hboundX := H.2.1 (point X m)
    have hb0 : |bump (r X₀ - m)| ≤ 1 := by
      rw [abs_of_nonneg (bump_nonneg _)]
      exact bump_le_one _
    calc
      _ = |(bump (r X - m) - bump (r X₀ - m)) * H.1 (point X m) +
            bump (r X₀ - m) * (H.1 (point X m) - H.1 (point X₀ m))| := by
              congr 1
              ring
      _ ≤ |(bump (r X - m) - bump (r X₀ - m)) * H.1 (point X m)| +
            |bump (r X₀ - m) * (H.1 (point X m) - H.1 (point X₀ m))| := abs_add_le _ _
      _ = |bump (r X - m) - bump (r X₀ - m)| *
            |H.1 (point X m)| + |bump (r X₀ - m)| *
            |H.1 (point X m) - H.1 (point X₀ m)| := by rw [abs_mul, abs_mul]
      _ ≤ τ * 1 + 1 * τ := by
            have hdiffH : |H.1 (point X m) - H.1 (point X₀ m)| ≤ τ :=
              hHlip.trans (le_of_lt hn.2)
            have hfirst :
                |bump (r X - m) - bump (r X₀ - m)| * |H.1 (point X m)| ≤ τ * 1 := by
              calc
                _ ≤ τ * |H.1 (point X m)| :=
                  mul_le_mul_of_nonneg_right hn.1.le (abs_nonneg _)
                _ ≤ τ * 1 := mul_le_mul_of_nonneg_left hboundX (le_of_lt hτ)
            have hsecond :
                |bump (r X₀ - m)| * |H.1 (point X m) - H.1 (point X₀ m)| ≤ 1 * τ :=
              mul_le_mul hb0 hdiffH (abs_nonneg _) (by norm_num)
            exact add_le_add hfirst hsecond
      _ = 2 * τ := by ring
  have hsumdiff : |linearizedObservableLift D hs H.1 X -
      linearizedObservableLift D hs H.1 X₀| ≤ (I.card : ℝ) * (2 * τ) := by
    rw [hsumY, hsum0]
    calc
      |(∑ m ∈ I, bump (r X - m) * H.1 (point X m)) -
        (∑ m ∈ I, bump (r X₀ - m) * H.1 (point X₀ m))| =
        |∑ m ∈ I, (bump (r X - m) * H.1 (point X m) -
          bump (r X₀ - m) * H.1 (point X₀ m))| := by rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ m ∈ I, |bump (r X - m) * H.1 (point X m) -
          bump (r X₀ - m) * H.1 (point X₀ m)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ I, 2 * τ := by
        apply Finset.sum_le_sum
        intro m hm
        exact hterm m hm
      _ = (I.card : ℝ) * (2 * τ) := by simp
  have hsmall : (I.card : ℝ) * (2 * τ) < ε := by
    dsimp [τ]
    have hc : (I.card : ℝ) < (I.card : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_self _
    have hratio : (I.card : ℝ) / (2 * ((I.card : ℝ) + 1)) < 1 / 2 := by
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith
    calc
      (I.card : ℝ) * (2 * (ε / (4 * ((I.card : ℝ) + 1)))) =
          ((I.card : ℝ) / (2 * ((I.card : ℝ) + 1))) * ε := by
        have hden : (4 : ℝ) + (I.card : ℝ) * 4 ≠ 0 := by positivity
        field_simp
        <;> ring
      _ < (1 / 2) * ε := mul_lt_mul_of_pos_right hratio hε
      _ < ε := by linarith
  exact lt_of_le_of_lt hsumdiff hsmall

/-- A uniform neighborhood estimate for an invariant lift descends to any
compatible metric on the quotient. -/
theorem ObservableDescent.equicontinuous_of_lift {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G}
    [MetricSpace (G ⧸ Γ)] {Y : Type*} [MetricSpace Y]
    (O : ObservableDescent G Γ Y)
    (hmetric : QuotientGroup.instTopologicalSpace Γ =
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace)
    (hloc : ∀ g ε, 0 < ε →
      ∃ U ∈ 𝓝 g, ∀ g' ∈ U, ∀ H : LipOne Y,
        |O.lift H.1 g' - O.lift H.1 g| < ε) :
    ∀ x ε, 0 < ε →
      ∃ δ, 0 < δ ∧ ∀ y, dist y x < δ → ∀ H : LipOne Y,
        |O.desc H.1 y - O.desc H.1 x| < ε := by
  intro x ε hε
  refine Quotient.inductionOn x ?_
  intro g
  obtain ⟨U, hU, hclose⟩ := hloc g ε hε
  obtain ⟨V, hVU, hVopen, hgV⟩ := mem_nhds_iff.mp hU
  let q : G → G ⧸ Γ := QuotientGroup.mk
  have hqopen : IsOpen (q '' V) :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap V hVopen
  have hqg : q g ∈ q '' V := ⟨g, hgV, rfl⟩
  have hqmem : q '' V ∈ 𝓝 (q g) := hqopen.mem_nhds hqg
  have hqmemMetric : q '' V ∈
      @nhds (G ⧸ Γ)
        (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace (q g) := by
    rw [← hmetric]
    exact hqmem
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hqmemMetric
  refine ⟨δ, hδ, ?_⟩
  intro y hy H
  have hyball : y ∈ Metric.ball (q g) δ := by
    simpa [Metric.mem_ball, dist_comm] using hy
  obtain ⟨g', hg'V, hgy⟩ := hball hyball
  calc
    |O.desc H.1 y - O.desc H.1 (q g)| =
        |O.desc H.1 (q g') - O.desc H.1 (q g)| := by rw [← hgy]
    _ = |O.lift H.1 g' - O.lift H.1 g| := by rw [O.desc_mk, O.desc_mk]
    _ < ε := hclose g' (hVU hg'V) H

private theorem realTranslationElement_zero {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s) :
    realTranslationElement F hs 0 = 1 := by
  apply NilpotentLieBCHGroup.ext
  simp [realTranslationElement]

private theorem realTranslationElement_zpow {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s) (hs : 0 < s)
    (n : ℤ) :
    (realTranslationElement F hs 1) ^ n = realTranslationElement F hs (n : ℝ) := by
  induction n using Int.induction_on with
  | zero => simpa using (realTranslationElement_zero F hs).symm
  | succ n ih =>
      rw [zpow_add_one, ih, realTranslationElement_mul]
      congr 1
      push_cast
      ring
  | pred n ih =>
      rw [zpow_sub_one, ih]
      have hmul : realTranslationElement F hs (-1) * realTranslationElement F hs 1 =
          realTranslationElement F hs 0 := by
        simpa using realTranslationElement_mul F hs (-1) 1
      have hmulOne : realTranslationElement F hs (-1) *
          realTranslationElement F hs 1 = 1 := by
        rw [hmul, realTranslationElement_zero]
      have hinv : (realTranslationElement F hs 1)⁻¹ = realTranslationElement F hs (-1) := by
        exact ((mul_eq_one_iff_eq_inv).mp hmulOne).symm
      rw [hinv]
      push_cast
      rw [realTranslationElement_mul F hs (-(n : ℝ)) (-1)]
      congr 1

/-- At an integer orbit point the interpolation selects exactly the matching
evaluation of the adapted polynomial log. -/
private theorem linearizedObservableLift_orbit_eval {L : Type*} [LieRing L]
    [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 0 < s)
    (H : D.Space → ℝ)
    (xhat : (weightFiltration D.filtration hs).realification.Group)
    (hxhat : realTranslationCoordinate D.filtration xhat.coord = 0)
    (P : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (hEval : ∀ n : ℤ,
      evLinReal D.filtration n xhat.coord = VectorPolynomial.eval
        (fun _ : Unit => (n : ℚ)) P)
    (n : ℤ) :
    linearizedObservableLift D hs H
        ((realTranslationElement D.filtration hs 1) ^ n * xhat) =
      H (QuotientGroup.mk
        (⟨VectorPolynomial.eval (fun _ : Unit => (n : ℚ)) P⟩ : D.filtration.realification.Group)) := by
  let F := D.filtration
  let g := realTranslationElement F hs 1
  let X := g ^ n * xhat
  have hpow : g ^ n = realTranslationElement F hs (n : ℝ) :=
    realTranslationElement_zpow F hs n
  have hr : realTranslationCoordinate F X.coord = (n : ℝ) := by
    dsimp [X]
    change realTranslationCoordinate F (lieBCH (2 * s) (g ^ n).coord xhat.coord) = _
    rw [realTranslationCoordinate_lieBCH F hs, hpow,
      realTranslationElement_coord F hs, hxhat]
    simp
  have hcancel : realTranslationElement F hs (-n : ℝ) * X = xhat := by
    dsimp [X]
    rw [hpow]
    calc
      realTranslationElement F hs (-n : ℝ) *
          (realTranslationElement F hs (n : ℝ) * xhat) =
          (realTranslationElement F hs (-n : ℝ) *
            realTranslationElement F hs (n : ℝ)) * xhat := by group
      _ = realTranslationElement F hs 0 * xhat := by
            rw [realTranslationElement_mul]
            congr 1
            ring
      _ = xhat := by rw [realTranslationElement_zero, one_mul]
  have hpoint : linearizedObservablePoint D hs n X =
      QuotientGroup.mk
        (⟨VectorPolynomial.eval (fun _ : Unit => (n : ℚ)) P⟩ : D.filtration.realification.Group) := by
    unfold linearizedObservablePoint
    change QuotientGroup.mk
      (⟨evLinReal F n
        ((⟨-realTranslationCoordinate F X.coord • realDhat F⟩ * X).coord)⟩ :
          F.realification.Group) = _
    rw [hr]
    change QuotientGroup.mk
      (⟨evLinReal F n (realTranslationElement F hs (-n : ℝ) * X).coord⟩ :
        F.realification.Group) = _
    rw [hcancel, hEval n]
  have hzero (m : ℤ) (hm : m ≠ n) :
      bump (realTranslationCoordinate F X.coord - m) = 0 := by
    rw [hr]
    have hsepInt : (1 : ℤ) ≤ |n - m| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hm))
    have hsep : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by exact_mod_cast hsepInt
    have hlarge : (1 / 3 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by linarith
    have hnonpos : 1 - 3 * |(n : ℝ) - (m : ℝ)| ≤ 0 := by nlinarith [hlarge]
    unfold bump
    rw [max_eq_left hnonpos]
  unfold linearizedObservableLift
  rw [liftObs_at_integer _ _ H X n hr hzero, hpoint]

/-- The compactness/equicontinuity construction equips the quotient with a
compatible metric for which every descended Lipschitz observable has a uniform
Lipschitz constant.  This is IB.a10. -/
theorem exists_observable_menuMetric {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : Subgroup G} [MetricSpace (G ⧸ Γ)]
    [CompactSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)] {Y : Type*} [MetricSpace Y]
    (O : ObservableDescent G Γ Y)
    (hmetric : QuotientGroup.instTopologicalSpace Γ =
      (inferInstance : MetricSpace (G ⧸ Γ)).toUniformSpace.toTopologicalSpace)
    (heq : ∀ x ε, 0 < ε →
      ∃ δ, 0 < δ ∧ ∀ y, dist y x < δ → ∀ H : LipOne Y,
          |O.desc H.1 y - O.desc H.1 x| < ε) :
    ∃ d : MetricSpace (G ⧸ Γ),
      QuotientGroup.instTopologicalSpace Γ = d.toUniformSpace.toTopologicalSpace ∧
      ∀ (H : Y → ℝ), (∀ y, |H y| ≤ 1) → ∀ (K₁ : ℝ≥0),
        LipschitzWith K₁ H →
          letI := d
          LipschitzWith (max 1 K₁) (O.desc H) := by
  classical
  letI : TopologicalSpace (LipOne Y) := ⊥
  letI : DiscreteTopology (LipOne Y) := ⟨rfl⟩
  let liftAt (x : G ⧸ Γ) : LipOne Y →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfDiscrete (fun H => O.desc H.1 x) 2 (by
      intro H J
      have hH := O.unit_bound H.1 H.2.1 x
      have hJ := O.unit_bound J.1 J.2.1 x
      rw [dist_eq_norm, Real.norm_eq_abs]
      calc
        |O.desc H.1 x - O.desc J.1 x| ≤
            |O.desc H.1 x| + |O.desc J.1 x| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hH hJ
        _ = 2 := by norm_num)
  have hLiftCont : Continuous liftAt := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := heq x (ε / 2) (by linarith)
    have hopen : IsOpen (Metric.ball x δ) := by
      rw [hmetric]
      exact Metric.isOpen_ball
    have hmem : Metric.ball x δ ∈ 𝓝 x := hopen.mem_nhds (by simp [hδ])
    filter_upwards [hmem] with y hy
    have hyDist : dist y x < δ := by simpa [Metric.mem_ball, dist_comm] using hy
    have hdist : dist (liftAt y) (liftAt x) ≤ ε / 2 := by
      apply (BoundedContinuousFunction.dist_le (by positivity)).2
      intro H
      have hpt := hnear y hyDist H
      calc
        dist (liftAt y H) (liftAt x H) =
            |O.desc H.1 y - O.desc H.1 x| := by
              simp [liftAt, BoundedContinuousFunction.mkOfDiscrete_apply,
                dist_eq_norm, Real.norm_eq_abs]
        _ ≤ ε / 2 := le_of_lt hpt
    exact lt_of_le_of_lt hdist (by linarith)
  let Φ : (G ⧸ Γ) → (G ⧸ Γ) × (LipOne Y →ᵇ ℝ) := fun x => (x, liftAt x)
  letI : MetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) := inferInstance
  have hΦcont : Continuous Φ := continuous_id.prodMk hLiftCont
  have hΦinj : Function.Injective Φ := fun x y h => (Prod.mk.inj h).1
  have hEmbed : Topology.IsEmbedding Φ := hΦcont.isClosedEmbedding hΦinj |>.isEmbedding
  have hprodTop : (instTopologicalSpaceProd :
      TopologicalSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ))) =
      (inferInstance : MetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ))).toUniformSpace.toTopologicalSpace := by
    rw [hmetric]
    with_reducible_and_instances rfl
  letI quotientBaseMetric : MetricSpace (G ⧸ Γ) := inferInstance
  letI quotientBasePseudo : PseudoMetricSpace (G ⧸ Γ) :=
    quotientBaseMetric.toPseudoMetricSpace
  letI observableBaseMetric : MetricSpace (LipOne Y →ᵇ ℝ) := inferInstance
  letI observableBasePseudo : PseudoMetricSpace (LipOne Y →ᵇ ℝ) :=
    observableBaseMetric.toPseudoMetricSpace
  letI productMetric : MetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) := inferInstance
  letI productPseudoMetric : PseudoMetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) :=
    productMetric.toPseudoMetricSpace
  letI productPseudoEMetric : PseudoEMetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) :=
    productPseudoMetric.toPseudoEMetricSpace
  have hEmbedMetric : @Topology.IsEmbedding (G ⧸ Γ)
      ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ)) (QuotientGroup.instTopologicalSpace Γ)
      ((inferInstance : MetricSpace ((G ⧸ Γ) × (LipOne Y →ᵇ ℝ))).toUniformSpace.toTopologicalSpace) Φ := by
    have h := hEmbed
    rw [hprodTop] at h
    exact h
  let d : MetricSpace (G ⧸ Γ) := Topology.IsEmbedding.comapMetricSpace Φ hEmbedMetric
  letI dMetric : MetricSpace (G ⧸ Γ) := d
  letI dPseudoMetric : PseudoMetricSpace (G ⧸ Γ) := d.toPseudoMetricSpace
  letI dPseudoEMetric : PseudoEMetricSpace (G ⧸ Γ) := dPseudoMetric.toPseudoEMetricSpace
  have htop : QuotientGroup.instTopologicalSpace Γ = d.toUniformSpace.toTopologicalSpace := rfl
  have hΦlip : LipschitzWith 1 Φ := by
    have hIso : Isometry Φ := by
      exact hEmbedMetric.to_isometry
    exact hIso.lipschitzWith
  have hcoord (H : LipOne Y) : LipschitzWith 1 (fun x => O.desc H.1 x) := by
    have hSnd : LipschitzWith 1 (@Prod.snd (G ⧸ Γ) (LipOne Y →ᵇ ℝ)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change @dist (LipOne Y →ᵇ ℝ) observableBasePseudo.toDist x.2 y.2 ≤
        (1 : ℝ) * max (@dist (G ⧸ Γ) quotientBasePseudo.toDist x.1 y.1)
          (@dist (LipOne Y →ᵇ ℝ) observableBasePseudo.toDist x.2 y.2)
      calc
        @dist (LipOne Y →ᵇ ℝ) observableBasePseudo.toDist x.2 y.2 ≤
            max (@dist (G ⧸ Γ) quotientBasePseudo.toDist x.1 y.1)
              (@dist (LipOne Y →ᵇ ℝ) observableBasePseudo.toDist x.2 y.2) := le_max_right _ _
        _ = (1 : ℝ) * max (@dist (G ⧸ Γ) quotientBasePseudo.toDist x.1 y.1)
              (@dist (LipOne Y →ᵇ ℝ) observableBasePseudo.toDist x.2 y.2) := by ring
    have h := (BoundedContinuousFunction.lipschitz_eval_const H).comp
      (hSnd.comp hΦlip)
    simpa [Φ, liftAt, BoundedContinuousFunction.mkOfDiscrete_apply,
      Function.comp_def] using h
  refine ⟨d, htop, ?_⟩
  ·
      intro H hH K₁ hLip
      let K : ℝ≥0 := max 1 K₁
      have hKone : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_left 1 K₁)
      have hK₁ : (K₁ : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_right 1 K₁)
      have hKpos : 0 < (K : ℝ) := lt_of_lt_of_le (by norm_num) hKone
      have hHnBound : ∀ y, |H y / (K : ℝ)| ≤ 1 := by
        intro y
        rw [abs_div, abs_of_pos hKpos]
        exact (div_le_one hKpos).2 ((hH y).trans hKone)
      have hHd (x y : Y) : |H x - H y| ≤ (K₁ : ℝ) * dist x y := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul x y
      have hHnLip : LipschitzWith 1 (fun y => H y / (K : ℝ)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        change |H x / (K : ℝ) - H y / (K : ℝ)| ≤ (1 : ℝ) * dist x y
        calc
          |H x / (K : ℝ) - H y / (K : ℝ)| = |H x - H y| / (K : ℝ) := by
            rw [← sub_div, abs_div, abs_of_pos hKpos]
          _ ≤ ((K₁ : ℝ) * dist x y) / (K : ℝ) :=
            div_le_div_of_nonneg_right (hHd x y) (le_of_lt hKpos)
          _ = ((K₁ : ℝ) / (K : ℝ)) * dist x y := by ring
          _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right
            ((div_le_one hKpos).2 hK₁) dist_nonneg
      let Hn : LipOne Y := ⟨fun y => H y / (K : ℝ), hHnBound, hHnLip⟩
      have hscaled : LipschitzWith K (fun z : ℝ => (K : ℝ) * z) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        change dist ((K : ℝ) * x) ((K : ℝ) * y) ≤ (K : ℝ) * dist x y
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
        simpa [Real.norm_eq_abs, abs_of_nonneg K.2]
      have hdesc : O.desc H = fun x => (K : ℝ) * O.desc Hn.1 x := by
        funext x
        have hfun : (fun y => (K : ℝ) * Hn.1 y) = H := by
          funext y
          dsimp [Hn]
          field_simp [ne_of_gt hKpos]
        calc
          O.desc H x = O.desc (fun y => (K : ℝ) * Hn.1 y) x := by rw [← hfun]
          _ = (K : ℝ) * O.desc Hn.1 x := O.scale (K : ℝ) Hn.1 x
      have hDescLip : LipschitzWith K (O.desc H) := by
        rw [hdesc]
        simpa [Function.comp_def] using hscaled.comp (hcoord Hn)
      simpa [K] using hDescLip

end HindmanSumsProducts.InverseBridge
