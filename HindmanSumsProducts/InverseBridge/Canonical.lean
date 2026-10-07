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

private def baseDataBracketAt {s : ℕ} (δ : BaseData s) (i j k : ℕ) : ℚ :=
  if hi : i < δ.d then
    if hj : j < δ.d then
      if hk : k < δ.d then δ.bracket ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ else 0
    else 0
  else 0

private def baseDataRowAt {s : ℕ} (δ : BaseData s) (i : Fin (s + 1))
    (j k : ℕ) : ℚ :=
  if hj : j < δ.d then
    if hk : k < δ.d then δ.rows i ⟨j, hj⟩ ⟨k, hk⟩ else 0
  else 0

private theorem finite_rationalLogHeight (p : ℝ) :
    {q : ℚ | rationalLogHeight q ≤ p}.Finite := by
  classical
  let N := ⌈Real.exp p⌉₊
  let candidates : Finset ℚ :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).biUnion fun a =>
      (Finset.Icc 1 N).image fun b : ℕ => (a : ℚ) / (b : ℚ)
  apply candidates.finite_toSet.subset
  intro q hq
  have hheight : RationalHeightLE q N := by
    simpa [N] using rationalHeightLE_ceil_exp hq
  have habs : (q.num.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hheight.1
  have hup : q.num ≤ (N : ℤ) := Int.le_natAbs.trans habs
  have hlow : -(N : ℤ) ≤ q.num := by
    by_cases hq0 : 0 ≤ q.num
    · omega
    · have hqneg : q.num ≤ 0 := le_of_not_ge hq0
      rw [Int.eq_neg_natAbs_of_nonpos hqneg]
      exact neg_le_neg habs
  have hmem : q ∈ candidates := by
    refine Finset.mem_biUnion.mpr ⟨q.num, Finset.mem_Icc.mpr ⟨hlow, hup⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨q.den, Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr q.den_ne_zero, hheight.2⟩, ?_⟩
    exact q.num_div_den
  exact hmem

private abbrev BoundedRational (p : ℝ) := {q : ℚ // rationalLogHeight q ≤ p}

private abbrev BaseDataCode (s d N : ℕ) (p : ℝ) :=
  (Fin d → Fin d → Fin d → BoundedRational p) ×
    (Fin (s + 1) → Fin (d + 1)) ×
    (Fin (s + 1) → Fin d → Fin d → BoundedRational p) × Fin (N + 1)

private abbrev BaseDataCodeBundle (s dmax N : ℕ) (p : ℝ) :=
  Σ d : Fin (dmax + 1), BaseDataCode s d.val N p

private def decodeBaseDataCode {s d N : ℕ} {p : ℝ}
    (C : BaseDataCode s d N p) : BaseData s where
  d := d
  bracket := fun i j k => (C.1 i j k).val
  rank := fun i => (C.2.1 i).val
  rows := fun i j k => (C.2.2.1 i j k).val
  grid := C.2.2.2.val

private def decodeBaseDataCodeBundle {s dmax N : ℕ} {p : ℝ}
    (C : BaseDataCodeBundle s dmax N p) : BaseData s :=
  decodeBaseDataCode C.2

/-- Bounded geometry complexity admits only finitely many finite shadows. -/
theorem baseData_finite (s : ℕ) (p : ℝ) :
    {δ : BaseData s | ∃ (L : Type*) (hL : LieRing L) (hA : LieAlgebra ℚ L),
      letI : LieRing L := hL
      letI : LieAlgebra ℚ L := hA
      ∃ D : RationalFilteredNilmanifold L s δ.d,
        D.GeometryComplexityLE p ∧ baseData D = δ}.Finite := by
  classical
  let dmax : ℕ := ⌈p⌉₊
  let N : ℕ := ⌈Real.exp p⌉₊
  letI : Fintype (BoundedRational p) := (finite_rationalLogHeight p).fintype
  letI : Fintype (BaseDataCodeBundle s dmax N p) := inferInstance
  apply (Set.finite_range (decodeBaseDataCodeBundle (s := s) (dmax := dmax)
    (N := N) (p := p))).subset
  intro δ hδ
  rcases hδ with ⟨L, hL, hA, hDData⟩
  letI : LieRing L := hL
  letI : LieAlgebra ℚ L := hA
  rcases hDData with ⟨D, hD, hEq⟩
  have hp : 0 ≤ p := by
    have hd : (0 : ℝ) ≤ (δ.d : ℝ) := Nat.cast_nonneg _
    linarith [hD.1]
  have hdBound : δ.d ≤ dmax := by
    have hceil : p ≤ (dmax : ℝ) := by
      dsimp [dmax]
      exact Nat.le_ceil p
    exact_mod_cast hD.1.trans hceil
  have hgridBound : D.grid ≤ N := by
    have hceil : Real.exp p ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil (Real.exp p)
    exact_mod_cast hD.2.1.trans hceil
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hdimL : Module.finrank ℚ L = δ.d := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis D.basis
  have hrank (i : Fin (s + 1)) :
      Module.finrank ℚ (D.filtration.layer (i.val + 1)) ≤ δ.d := by
    calc
      Module.finrank ℚ (D.filtration.layer (i.val + 1)) ≤ Module.finrank ℚ L :=
        Submodule.finrank_le _
      _ = δ.d := hdimL
  have hrow (i : Fin (s + 1)) (j k : Fin δ.d) :
      rationalLogHeight ((baseData D).rows i j k) ≤ p := by
    dsimp [baseData]
    split_ifs with hj
    · exact hD.2.2.2 i ⟨j.val, hj⟩ k
    · simpa [rationalLogHeight] using hp
  let code : BaseDataCode s δ.d N p :=
    ( (fun i j k => ⟨(baseData D).bracket i j k, by
          simpa [baseData] using hD.2.2.1 i j k⟩),
      (fun i => ⟨(baseData D).rank i, Nat.lt_succ_of_le (hrank i)⟩),
      (fun i j k => ⟨(baseData D).rows i j k, hrow i j k⟩),
      ⟨D.grid, Nat.lt_succ_of_le hgridBound⟩ )
  let bundle : BaseDataCodeBundle s dmax N p :=
    ⟨⟨δ.d, Nat.lt_succ_of_le hdBound⟩, code⟩
  refine ⟨bundle, ?_⟩
  change decodeBaseDataCode code = δ
  calc
    decodeBaseDataCode code = baseData D := by
      rfl
    _ = δ := hEq

/-- A finite datum is realizable when it is the shadow of an OAI base model. -/
def Realizable {s : ℕ} (δ : BaseData s) : Prop :=
  ∃ (L : Type*) (hL : LieRing L) (hA : LieAlgebra ℚ L),
    letI : LieRing L := hL
    letI : LieAlgebra ℚ L := hA
    ∃ D : RationalFilteredNilmanifold L s δ.d, baseData D = δ

/-- A datum realized by some base model whose geometry is bounded by `p`. -/
def RealizableAt {s : ℕ} (p : ℝ) (δ : BaseData s) : Prop :=
  ∃ (L : Type) (hL : LieRing L) (hA : LieAlgebra ℚ L),
    letI : LieRing L := hL
    letI : LieAlgebra ℚ L := hA
    ∃ D : RationalFilteredNilmanifold L s δ.d,
      D.GeometryComplexityLE p ∧ baseData D = δ

/-- Equal finite data determine a filtered Lie isomorphism matching the chosen bases. -/
theorem exists_dataEquiv {s d : ℕ} {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s d)
    (h : baseData D = baseData E) :
    ∃ φ : L ≃ₗ⁅ℚ⁆ M,
      (∀ i, φ (D.basis i) = E.basis i) ∧
      ∀ k a, a ∈ D.filtration.layer k ↔ φ a ∈ E.filtration.layer k := by
  have hbracket (i j k : Fin d) :
      lieStructureConstants D.basis i j k = lieStructureConstants E.basis i j k := by
    have heq := congrArg (fun B : BaseData s =>
      baseDataBracketAt B i.val j.val k.val) h
    simpa [baseDataBracketAt, baseData, i.isLt, j.isLt, k.isLt] using heq
  have hrow (i : Fin (s + 1)) (j k : Fin d) :
      (baseData D).rows i j k = (baseData E).rows i j k := by
    have heq := congrArg (fun B : BaseData s => baseDataRowAt B i j.val k.val) h
    simpa [baseDataRowAt, baseData, j.isLt, k.isLt] using heq
  have hrowRepD (i : Fin (s + 1)) (j k : Fin d) :
      D.basis.repr (D.paddedLayerVector i j) k = (baseData D).rows i j k := by
    by_cases hj : j.val < Module.finrank ℚ (D.filtration.layer (i.val + 1))
    · simp [baseData, RationalFilteredNilmanifold.paddedLayerVector, hj]
    · simp [baseData, RationalFilteredNilmanifold.paddedLayerVector, hj]
  have hrowRepE (i : Fin (s + 1)) (j k : Fin d) :
      E.basis.repr (E.paddedLayerVector i j) k = (baseData E).rows i j k := by
    by_cases hj : j.val < Module.finrank ℚ (E.filtration.layer (i.val + 1))
    · simp [baseData, RationalFilteredNilmanifold.paddedLayerVector, hj]
    · simp [baseData, RationalFilteredNilmanifold.paddedLayerVector, hj]
  have hcoordinates : D.rationalModelCoordinates = E.rationalModelCoordinates := by
    funext z
    rcases z with z | z
    · exact hbracket z.1 z.2.1 z.2.2
    · change D.basis.repr (D.paddedLayerVector z.1 z.2.1) z.2.2 =
        E.basis.repr (E.paddedLayerVector z.1 z.2.1) z.2.2
      rw [hrowRepD, hrow, ← hrowRepE]
  let φ := D.rationalModelEquiv E hcoordinates
  refine ⟨φ, D.rationalModelEquiv_basis E hcoordinates, ?_⟩
  intro k a
  have hlayer := D.rationalModelEquiv_layer E hcoordinates k
  constructor
  · intro ha
    rw [← hlayer]
    exact ⟨a, ha, rfl⟩
  · intro ha
    rw [← hlayer] at ha
    rcases (Submodule.mem_map.mp ha) with ⟨b, hb, hba⟩
    have hba' : b = a := φ.injective hba
    simpa [hba'] using hb

/-- A canonical coordinate sublattice, with its coordinate grid divisible by
the original grid and contained in the original lattice.  This is IB.c3. -/
theorem exists_canonical_lattice {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d) :
    ∃ B : ℕ, 0 < B ∧ D.grid ∣ B ∧
      ∃ Λ : Subgroup D.filtration.Group,
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧ Λ ≤ D.lattice := by
  classical
  let H : ℕ := ∑ ijk : Fin d × Fin d × Fin d,
    max (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).num.natAbs
      (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).den
  have hheight (i j k : Fin d) :
      RationalHeightLE (lieStructureConstants D.basis i j k) H := by
    have hs : max (lieStructureConstants D.basis i j k).num.natAbs
        (lieStructureConstants D.basis i j k).den ≤ H := by
      change max (lieStructureConstants D.basis i j k).num.natAbs
          (lieStructureConstants D.basis i j k).den ≤
        ∑ ijk : Fin d × Fin d × Fin d,
          max (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).num.natAbs
            (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).den
      exact Finset.single_le_sum
        (f := fun ijk : Fin d × Fin d × Fin d =>
          max (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).num.natAbs
            (lieStructureConstants D.basis ijk.1 ijk.2.1 ijk.2.2).den)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j, k))
    exact ⟨(Nat.le_max_left _ _).trans hs, (Nat.le_max_right _ _).trans hs⟩
  obtain ⟨B, Λ, hB, hdiv, _, hsub, hcoords⟩ :=
    exists_integral_grid_subgroup D.basis D.filtration.lowerCentralSeries_eq_bot
      D.lattice D.grid D.grid_pos hheight D.inner_grid
  exact ⟨B, hB, hdiv, Λ, hcoords, hsub⟩

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
    (E : RationalFilteredNilmanifold M s d)
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.normBound ≤ 1)
    (u : ℂ) (hu : ‖u‖ = 1)
    (π : E.Space → D.Space)
    (p : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (C : ℝ≥0)
    (hπ : letI := E.metricSpace; letI := D.metricSpace; LipschitzWith C π)
    (horbit : ∀ n : ℤ, π (E.integerOrbitPoint p n) = D.integerOrbitPoint T.orbit n) :
    ∃ H : E.Space → ℝ,
      (∀ y, H y ∈ Set.Icc (0 : ℝ) 1) ∧
      (letI := E.metricSpace
       LipschitzWith (T.lipBound * C / 2) H) ∧
      ∀ n : ℤ, H (E.integerOrbitPoint p n) =
        (1 + (u * T.eval (fun _ => n)).re) / 2 := by
  letI := D.metricSpace
  letI := E.metricSpace
  let H : E.Space → ℝ := fun y => (1 + (u * T.observable (π y)).re) / 2
  have hnorm (y : E.Space) : ‖u * T.observable (π y)‖ ≤ 1 := by
    calc
      ‖u * T.observable (π y)‖ = ‖u‖ * ‖T.observable (π y)‖ := norm_mul _ _
      _ = ‖T.observable (π y)‖ := by rw [hu]; ring
      _ ≤ (T.normBound : ℝ) := T.norm_le _
      _ ≤ 1 := by exact_mod_cast hT
  have hreal (y : E.Space) : |(u * T.observable (π y)).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans (hnorm y)
  have hmul : LipschitzWith 1 (fun z : ℂ => u * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hu]
    simp
  have hrot : LipschitzWith (1 / 2) (fun z : ℂ => (1 + (u * z).re) / 2) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hRe : LipschitzWith 1 (fun z : ℂ => (u * z).re) :=
      by simpa [Function.comp_def, RCLike.re_eq_complex_re] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp hmul
    calc
      dist ((1 + (u * z).re) / 2) ((1 + (u * w).re) / 2) =
          dist ((u * z).re) ((u * w).re) / 2 := by
            rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
            rw [show (1 + (u * z).re) / 2 - (1 + (u * w).re) / 2 =
              ((u * z).re - (u * w).re) / 2 by ring]
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (1 / 2 : ℝ) * dist z w := by
          calc
            _ ≤ (1 * dist z w) / 2 := by gcongr; exact hRe.dist_le_mul z w
            _ = (1 / 2 : ℝ) * dist z w := by ring
  have hTπ : LipschitzWith (T.lipBound * C) (fun y => T.observable (π y)) :=
    T.lipschitz.comp hπ
  have hLipH : LipschitzWith ((1 / 2) * (T.lipBound * C)) H := by
    simpa [H, Function.comp_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hrot.comp hTπ
  have hK : T.lipBound * C / 2 = (1 / 2) * (T.lipBound * C) := by
    apply Subtype.ext
    norm_cast
    ring
  refine ⟨H, ?_, ?_, ?_⟩
  · intro y
    have hr := abs_le.mp (hreal y)
    constructor
    · dsimp [H]
      linarith [hr.1]
    · dsimp [H]
      linarith [hr.2]
  · rw [hK]
    exact hLipH
  · intro n
    change (1 + (u * T.observable (π (E.integerOrbitPoint p n))).re) / 2 =
      (1 + (u * T.eval (fun _ => n)).re) / 2
    rw [horbit n]
    rfl

end HindmanSumsProducts.InverseBridge
