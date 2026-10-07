import HindmanSumsProducts.Prediction.Subgroup

open scoped BigOperators NNReal Topology
open Filter MeasureTheory Finset

namespace HindmanSumsProducts.Prediction

noncomputable section

private noncomputable def p_h3_smallFinsetEquiv (m : ℕ) :
    {J : Finset (Fin m) // J.card < 2} ≃ Option (Fin m) := by
  classical
  refine
    { toFun := fun J => if h : J.1 = ∅ then none
        else some (J.1.min' (Finset.nonempty_iff_ne_empty.mpr h))
      invFun := fun x => ⟨x.elim ∅ fun i => {i}, by cases x <;> simp⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro J
    by_cases he : J.1 = ∅
    · simp [he]
      apply Subtype.ext
      exact he.symm
    · have hc0 : J.1.card ≠ 0 := by
        intro hc
        exact he (Finset.card_eq_zero.mp hc)
      have hc : J.1.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      apply Subtype.ext
      simp [hi]
  · intro x
    cases x with
    | none => simp
    | some i => simp

private theorem p_h3_smallFilter_card (m : ℕ) :
    (Finset.univ.filter fun J : Finset (Fin m) => J.card < 2).card = m + 1 := by
  classical
  let S := Finset.univ.filter fun J : Finset (Fin m) => J.card < 2
  let e : {J : Finset (Fin m) // J.card < 2} ≃ ↥S :=
    { toFun := fun J => ⟨J.1, by simp [S]; omega⟩
      invFun := fun J => ⟨J.1, by simpa [S] using J.2⟩
      left_inv := by intro J; apply Subtype.ext; rfl
      right_inv := by intro J; apply Subtype.ext; rfl }
  calc
    S.card = Fintype.card ↥S := (Fintype.card_coe S).symm
    _ = Fintype.card {J : Finset (Fin m) // J.card < 2} := (Fintype.card_congr e).symm
    _ = Fintype.card (Option (Fin m)) := Fintype.card_congr (p_h3_smallFinsetEquiv m)
    _ = m + 1 := by simp

theorem p_h3_nonsingleton_card (m : ℕ) :
    (Finset.univ.filter fun J : Finset (Fin m) => 2 ≤ J.card).card = 2 ^ m - m - 1 := by
  classical
  let S := Finset.univ.filter fun J : Finset (Fin m) => J.card < 2
  let L := Finset.univ.filter fun J : Finset (Fin m) => 2 ≤ J.card
  have hdisj : Disjoint L S := by
    rw [Finset.disjoint_left]
    intro J hJ hS
    simp only [L, S, Finset.mem_filter, Finset.mem_univ, true_and] at hJ hS
    omega
  have hunion : L ∪ S = Finset.univ := by
    ext J
    simp [L, S]
    omega
  have hcard : L.card + S.card = 2 ^ m := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h
    have htotal : (Finset.univ : Finset (Finset (Fin m))).card = 2 ^ m := by
      simpa using (Fintype.card_finset : Fintype.card (Finset (Fin m)) =
        2 ^ Fintype.card (Fin m))
    rw [htotal] at h
    omega
  have hScard : S.card = m + 1 := p_h3_smallFilter_card m
  change L.card = 2 ^ m - m - 1
  rw [hScard] at hcard
  omega

theorem p_h3_support_card (m : ℕ) :
    Fintype.card {J : Finset (Fin m) // 2 ≤ J.card} = 2 ^ m - m - 1 := by
  classical
  let S := Finset.univ.filter fun J : Finset (Fin m) => 2 ≤ J.card
  let e : {J : Finset (Fin m) // 2 ≤ J.card} ≃ ↥S :=
    { toFun := fun J => ⟨J.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.2⟩⟩
      invFun := fun J => ⟨J.1, (Finset.mem_filter.mp J.2).2⟩
      left_inv := by intro J; apply Subtype.ext; rfl
      right_inv := by intro J; apply Subtype.ext; rfl }
  calc
    Fintype.card {J : Finset (Fin m) // 2 ≤ J.card} = Fintype.card ↥S := Fintype.card_congr e
    _ = S.card := Fintype.card_coe S
    _ = 2 ^ m - m - 1 := p_h3_nonsingleton_card m

private def p_h3_finEmbedding {q sl : ℕ} (h : q ≤ sl) : Fin q ↪ Fin sl :=
  ⟨Fin.castLE h, by
    intro x y hxy
    apply Fin.ext
    have hv : (Fin.castLE h x).val = (Fin.castLE h y).val := congrArg Fin.val hxy
    simpa using hv⟩

theorem p_h3_master_test_data (m : ℕ) :
    ∃ sl : ℕ, ∃ Dm : Finset (IntegerPolynomial sl),
      (∀ P ∈ Dm, P ≠ 0) ∧
      (1 : IntegerPolynomial sl) ∈ Dm ∧
      ∀ (J : Finset (Fin m)) (hJ : 2 ≤ J.card), Allowed Dm (corrTemplate m J hJ) := by
  classical
  let 𝒥 : Finset {J : Finset (Fin m) // 2 ≤ J.card} := Finset.univ
  let q (J : {J : Finset (Fin m) // 2 ≤ J.card}) := (corrTemplate m J.1 J.2).q
  let sl := ∑ J ∈ 𝒥, (q J + 1)
  have hq (J : {J : Finset (Fin m) // 2 ≤ J.card}) : q J ≤ sl := by
    dsimp [sl]
    calc
      q J ≤ q J + 1 := Nat.le_succ _
      _ ≤ ∑ J' ∈ 𝒥, (q J' + 1) := by
        exact Finset.single_le_sum (s := 𝒥) (f := fun J' => q J' + 1)
          (fun J' hJ' => Nat.zero_le _) (Finset.mem_univ J)
  let emb (J : {J : Finset (Fin m) // 2 ≤ J.card}) : Fin (q J) ↪ Fin sl :=
    p_h3_finEmbedding (hq J)
  let Dm : Finset (IntegerPolynomial sl) :=
    {1} ∪ 𝒥.biUnion (fun J =>
      (corrTemplate m J.1 J.2).tests.image (fun P => MvPolynomial.rename (emb J) P))
  refine ⟨sl, Dm, ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with h1 | hrest
    · rcases Finset.mem_singleton.mp h1 with rfl
      norm_num
    · rcases Finset.mem_biUnion.mp hrest with ⟨J, hJ, himage⟩
      rcases Finset.mem_image.mp himage with ⟨Q, hQ, hPQ⟩
      subst P
      intro hzero
      have hEq : MvPolynomial.rename (emb J) Q = MvPolynomial.rename (emb J) 0 := by
        simpa using hzero
      have hQzero : Q = 0 :=
        MvPolynomial.rename_injective (emb J) (emb J).injective hEq
      exact (corrTemplate m J.1 J.2).tests_ne_zero Q hQ hQzero
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
  · intro J hJ
    let j : {J : Finset (Fin m) // 2 ≤ J.card} := ⟨J, hJ⟩
    refine ⟨emb j, ?_⟩
    intro P hP
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨P, hP, rfl⟩

#print axioms p_h3_master_test_data

end

end HindmanSumsProducts.Prediction
