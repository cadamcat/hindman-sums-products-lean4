import Mathlib.Algebra.Lie.TransferInstance
import HindmanSumsProducts.InverseBridge.Canonical

namespace HindmanSumsProducts.InverseBridge

open OAI OAI.Erdos3
open Module

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
  classical
  let V : Type := Fin d → ℚ
  let e0 : V ≃ₗ[ℚ] L := D.basis.equivFun.symm
  let hV : LieRing V := e0.toAddEquiv.lieRing
  letI : LieRing V := hV
  let hA : LieAlgebra ℚ V := e0.lieAlgebra
  letI : LieAlgebra ℚ V := hA
  let e : L ≃ₗ⁅ℚ⁆ V := (e0.lieEquiv ℚ).symm
  let b : Basis (Fin d) ℚ V := D.basis.map e.toLinearEquiv
  let F : NilpotentLieFiltration V s := {
    layer := fun n => (D.filtration.layer n).map e.toLinearEquiv.toLinearMap
    antitone := by
      intro i j hij
      exact Submodule.map_mono (D.filtration.antitone hij)
    one_eq_top := by
      apply le_antisymm
      · exact le_top
      · change (⊤ : Submodule ℚ V) ≤
          (D.filtration.layer 1).map e.toLinearEquiv.toLinearMap
        rw [D.filtration.one_eq_top, Submodule.map_top]
        exact le_of_eq (LinearMap.range_eq_top.mpr e.toLinearEquiv.surjective).symm
    lie_mem := by
      intro i j a c ha hc
      rcases Submodule.mem_map.mp ha with ⟨a', ha', rfl⟩
      rcases Submodule.mem_map.mp hc with ⟨c', hc', rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨⁅a', c'⁆, D.filtration.lie_mem ha' hc', ?_⟩
      exact e.map_lie a' c'
    terminal := by
      rw [D.filtration.terminal, Submodule.map_bot]
  }
  let layerEquiv (i : Fin (s + 1)) :
      D.filtration.layer (i.val + 1) ≃ₗ[ℚ] F.layer (i.val + 1) :=
    Submodule.equivMapOfInjective e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective (D.filtration.layer (i.val + 1))
  let rankEquiv (i : Fin (s + 1)) :
      Fin (Module.finrank ℚ (D.filtration.layer (i.val + 1))) ≃
        Fin (Module.finrank ℚ (F.layer (i.val + 1))) :=
    finCongr (LinearEquiv.finrank_map_eq e.toLinearEquiv
      (D.filtration.layer (i.val + 1))).symm
  let lb (i : Fin (s + 1)) :
      Basis (Fin (Module.finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)) :=
    (D.layerBasis i).map (layerEquiv i) |>.reindex (rankEquiv i)
  let mapG : D.filtration.Group →* F.Group :=
    NilpotentLieBCHGroup.map (hM := F.lowerCentralSeries_eq_bot) e.toLieHom
  let Λ : Subgroup F.Group := D.lattice.map mapG
  have hmatrix : LinearMap.toMatrix D.basis b e.toLieHom.toLinearMap = 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change D.basis.repr
      (e.toLinearEquiv.symm (e.toLinearEquiv (D.basis j))) i =
        (1 : Matrix (Fin d) (Fin d) ℚ) i j
    rw [LinearEquiv.symm_apply_apply]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hcoords : bchSubgroupCoordinates b Λ = bchSubgroupCoordinates D.basis D.lattice := by
    change bchSubgroupCoordinates b
      (D.lattice.map (NilpotentLieBCHGroup.map e.toLieHom)) = _
    rw [bchSubgroupCoordinates_map D.basis b e.toLieHom D.lattice, hmatrix]
    simp
  have heval (x : L) : e x = e.toLinearEquiv x :=
    (congrFun (LieEquiv.coe_toLinearEquiv e) x).symm
  have hrepr (x : L) : b.repr (e x) = D.basis.repr x := by
    rw [heval]
    simp [b, Basis.map]
    rw [heval]
    exact e.toLinearEquiv.symm_apply_apply x
  have hbr (i j k : Fin d) :
      lieStructureConstants b i j k = lieStructureConstants D.basis i j k := by
    rw [lieStructureConstants, lieStructureConstants]
    have hi : b i = e (D.basis i) := by simp [b]
    have hj : b j = e (D.basis j) := by simp [b]
    rw [hi, hj, ← e.map_lie, hrepr]
  have hrank (i : Fin (s + 1)) :
      Module.finrank ℚ (F.layer (i.val + 1)) =
        Module.finrank ℚ (D.filtration.layer (i.val + 1)) := by
    exact LinearEquiv.finrank_map_eq e.toLinearEquiv
      (D.filtration.layer (i.val + 1))
  have hlayerCoord (i : Fin (s + 1))
      (j : Fin (Module.finrank ℚ (F.layer (i.val + 1)))) (k : Fin d) :
      b.repr (lb i j) k =
        D.basis.repr (D.layerBasis i ((rankEquiv i).symm j)) k := by
    simp only [lb, Basis.reindex_apply, Basis.map_apply]
    change b.repr (e.toLinearEquiv
      (D.layerBasis i ((rankEquiv i).symm j))) k = _
    simpa using congrArg (fun v => v k) (hrepr (D.layerBasis i ((rankEquiv i).symm j)))
  let W : RationalFilteredNilmanifold V s d := {
    filtration := F
    basis := b
    layerBasis := lb
    lattice := Λ
    grid := D.grid
    grid_pos := D.grid_pos
    inner_grid := by
      simpa [hcoords] using D.inner_grid
    outer_grid := by
      simpa [hcoords] using D.outer_grid
  }
  refine ⟨V, hV, hA, ?_⟩
  letI : LieRing V := hV
  letI : LieAlgebra ℚ V := hA
  refine ⟨W, ?_, ?_⟩
  · have hbracket : (baseData W).bracket = (baseData D).bracket := by
      funext i j k
      simpa [baseData, W] using hbr i j k
    have hranks : (baseData W).rank = (baseData D).rank := by
      funext i
      simp [baseData, W, hrank]
    have hrows : (baseData W).rows = (baseData D).rows := by
      funext i j k
      dsimp [baseData, W]
      by_cases hD : j.val < Module.finrank ℚ (D.filtration.layer (i.val + 1))
      · have hW : j.val < Module.finrank ℚ (F.layer (i.val + 1)) := by
          rw [hrank]
          exact hD
        have hidx : (rankEquiv i).symm ⟨j.val, hW⟩ = ⟨j.val, hD⟩ := by
          apply Fin.ext
          rfl
        simp only [hD, hW]
        simpa [hidx] using hlayerCoord i ⟨j.val, hW⟩ k
      · have hW : ¬ j.val < Module.finrank ℚ (F.layer (i.val + 1)) := by
          rw [hrank]
          exact hD
        simp [hD, hW]
    have hbase : baseData W = baseData D := by
      simp only [baseData, W, BaseData.mk.injEq]
      exact ⟨trivial, heq_of_eq hbracket, hranks, heq_of_eq hrows, trivial⟩
    exact hbase
  · intro p
    constructor
    · rintro ⟨hd, hg, hc, hl⟩
      refine ⟨hd, ?_, ?_, ?_⟩
      · exact hg
      · intro i j k
        have h := hc i j k
        rw [hbr i j k] at h
        exact h
      · intro i j k
        have h := hl i (rankEquiv i j) k
        simpa [W, hlayerCoord] using h
    · rintro ⟨hd, hg, hc, hl⟩
      refine ⟨hd, ?_, ?_, ?_⟩
      · exact hg
      · intro i j k
        have h := hc i j k
        rw [← hbr i j k] at h
        exact h
      · intro i j k
        have h := hl i ((rankEquiv i).symm j) k
        simpa [W, hlayerCoord] using h

end HindmanSumsProducts.InverseBridge

-- #print axioms HindmanSumsProducts.InverseBridge.exists_small_model
